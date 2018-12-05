-- | Diffable trees, based on the paper [*Change Detection in
-- | Hierarchically Structured Information*](http://ilpubs.stanford.edu:8090/115/1/1995-46.pdf)
-- | by Sudarshan S. Chawathe, Anand Rajaraman, Hector Garcia-Molina, and
-- | Jennifer Widom, from *Proceedings of the ACM SIGMOD International
-- | Conference on Management of Data,* 1996.
-- |
-- | This module diverges from the paper in a few minor ways:
-- | * node IDs are kept as an internal implementation detail and not exposed
-- |   via the API,
-- | * Indices (e.g. of child nodes) are zero-based.
module Data.DiffableTree where

import Prelude

import Data.List (List)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))

withMaybe :: forall a. a -> (a -> Maybe a) -> a
withMaybe x f = fromMaybe x (f x)

-- TODO: how to handle missing node ids?

-- Based on the type in purescript-graphs. A graph whose vertices are labelled
-- by keys of type `k` and have values at each vertex of type `v`. Each vertex
-- is stored in a Map together with the vertex value as well as the keys of the
-- vertices which are immediately reachable from that vertex.
type Graph k v = Map k (Tuple v (List k))

newtype NodeId = NodeId Int

derive newtype instance eqNodeId :: Eq NodeId
derive newtype instance ordNodeId :: Ord NodeId

data DiffableTree a
  -- A diffable tree is a (non-empty) graph together with an identified root
  -- node id. We also store a mapping of node ids to their parent node ids.
  = DiffableTree NodeId (Graph NodeId a) (Map NodeId NodeId)

-- | The function `insertLeafNode childId value k parentId` inserts a new leaf
-- | node with id `childId` and value `value` as the `k`th child of the node
-- | with id `parentId` (zero-based).
-- |
-- | This function is likely to break the tree structure if the provided parent
-- | id does not exist in the tree, or if the provided child id already exists
-- | in the tree.
insertLeafNode :: forall a.
  NodeId -> a -> NodeId -> Int ->
    DiffableTree a -> DiffableTree a
insertLeafNode childId value parentId k (DiffableTree rootId tree parents) =
  let
    newChild =
      Tuple value List.Nil
    f (Tuple parentValue children) =
      Tuple parentValue (withMaybe children (List.insertAt k childId))
    newTree =
      tree
      # Map.update (Just <<< f) parentId
      # Map.insert childId newChild
    newParents =
      Map.insert childId parentId parents
  in
    DiffableTree rootId newTree newParents

-- | Delete the leaf node with the given id. If the given node id does not
-- | exist, this function does nothing. If the node is not a leaf node, this
-- | function will break the tree structure. The root node cannot be deleted.
deleteLeafNode :: forall a.
  NodeId -> DiffableTree a -> DiffableTree a
deleteLeafNode nodeId (DiffableTree rootId tree parents) =
  DiffableTree
    rootId
    (Map.delete nodeId tree)
    (Map.delete nodeId parents)

-- | Replaces the value at a given node with a new value. If the node id does
-- | not exist, this function does nothing.
updateNode :: forall a.
  NodeId -> a -> DiffableTree a -> DiffableTree a
updateNode nodeId newValue (DiffableTree rootId tree parents) =
  let
    f (Tuple _ children) = Tuple newValue children
  in
    DiffableTree
      rootId
      (Map.update (Just <<< f) nodeId tree)
      parents

-- | Move a subtree from one parent to another. The function `moveSubtree x y
-- | k` moves the entire subtree rooted at `x` to become the `k`th child of `y`
-- | (zero-based).
moveSubtree :: forall a.
  NodeId -> NodeId -> Int ->
    DiffableTree a -> DiffableTree a
moveSubtree subtreeId newParentId k (DiffableTree rootId tree parents) =
  case Map.lookup subtreeId parents of
    Just oldParentId ->
      let
        orphanSubtree =
          Map.update
            (\(Tuple v children) ->
                Just (Tuple v (List.delete subtreeId children)))
            oldParentId
        reinsertSubtree =
          Map.update
            (\(Tuple v children) ->
                Just (Tuple v (withMaybe children (List.insertAt k subtreeId))))
            newParentId
        newTree =
          tree
          # orphanSubtree
          # reinsertSubtree
        newParents =
          Map.update (Just <<< const newParentId) subtreeId parents
      in
        DiffableTree
          rootId
          newTree
          newParents
    Nothing ->
      -- should not happen
      DiffableTree rootId tree parents

data EditOperation a
  = Insert NodeId a NodeId Int
  | Delete NodeId
  | Update NodeId a
  | Move NodeId NodeId Int

derive instance eqEditOperation :: Eq a => Eq (EditOperation a)
derive instance ordEditOperation :: Ord a => Ord (EditOperation a)

apply :: forall a. EditOperation a -> DiffableTree a -> DiffableTree a
apply = case _ of
  Insert newId value parentId k ->
    insertLeafNode newId value parentId k
  Delete id ->
    deleteLeafNode id
  Update id value ->
    updateNode id value
  Move subtreeId newParentId k ->
    moveSubtree subtreeId newParentId k
