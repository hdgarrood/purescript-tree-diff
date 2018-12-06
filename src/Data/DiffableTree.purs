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

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as ST.Ref
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as Array.ST
import Data.Foldable (for_)
import Data.Function (on)
import Data.List (List)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe, fromJust)
import Data.Ord.Down (Down(..))
import Data.Profunctor.Strong (first, second)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Partial.Unsafe (unsafePartial)

paramF :: Number
paramF = 1.0

paramT :: Number
paramT = 0.5

withMaybe :: forall a. a -> (a -> Maybe a) -> a
withMaybe x f = fromMaybe x (f x)

-- Based on the type in purescript-graphs. A graph whose vertices are labelled
-- by keys of type `k` and have values at each vertex of type `v`. Each vertex
-- is stored in a Map together with the vertex value as well as the keys of the
-- vertices which are immediately reachable from that vertex.
type Graph k v = Map k (Tuple v (Array k))

newtype NodeId = NodeId Int

derive newtype instance eqNodeId :: Eq NodeId
derive newtype instance ordNodeId :: Ord NodeId

data DiffableTree a
  -- A diffable tree is a (non-empty) graph, which has no cycles, together with
  -- an identified root node id. We also store a mapping of node ids to their
  -- parent node ids; this information is redundant but maintained to enable
  -- fast querying.
  = DiffableTree NodeId (Graph NodeId a) (Map NodeId NodeId)

instance functorDiffableTree :: Functor DiffableTree where
  map f (DiffableTree rootId tree parents) =
    DiffableTree rootId (map (first f) tree) parents

type Node a =
  { value :: a
  , parent :: Maybe NodeId
  , children :: Array NodeId
  }

-- | Traverse a tree top-down, in a breadth-first order. We use an STRef for
-- | the tree, and the traversal is specialised to the ST monad, so that the
-- | tree can be modified during the traversal if necessary. The function
-- | argument is called once for each node, receiving the current depth
-- | (starting from 0 for the root) as well as the node's id.
-- |
-- | Inserting, deleting, or moving nodes during the traversal may result in
-- | unexpected behaviour, such as certain nodes being visited twice or not at
-- | all.
traverseTopDown :: forall r a.
  (Int -> NodeId -> ST r Unit) -> STRef r (DiffableTree a) -> ST r Unit
traverseTopDown visit treeRef = do
  queue <- Array.ST.empty
  DiffableTree rootId _ _ <- ST.Ref.read treeRef
  push (Tuple 0 rootId) queue

  ST.while (not <$> isEmpty queue) do
    Tuple depth id <- unsafePartial (fromJust <$> pop queue)
    visit depth id
    DiffableTree _ tree _ <- ST.Ref.read treeRef
    let children = maybe [] snd (Map.lookup id tree)
    Array.ST.pushAll (map (Tuple (depth+1)) children) queue

  where
  isEmpty = map (_ == Nothing) <<< Array.ST.peek 0

-- | Traverse a tree bottom-up and left-to-right (breadth-first). We use an
-- | STRef and the ST monad so that the tree can be modified during the
-- | traversal if necessary. The function argument is called once for each
-- | node, receiving the current depth (starting from 0 for the root) as well
-- | as the node's id.
-- |
-- | Inserting, deleting, or moving nodes during the traversal may result in
-- | unexpected behaviour in general, such as certain nodes being visited twice
-- | or not at all. However if, during the traversal, the current node is a
-- | leaf, it *can* be safely deleted.
traverseBottomUp :: forall r a.
  (Int -> NodeId -> ST r Unit) -> STRef r (DiffableTree a) -> ST r Unit
traverseBottomUp visit treeRef = do
  visitOrder <- computeVisitOrder
  for_ visitOrder (uncurry visit)

  where
  computeVisitOrder :: ST r (Array (Tuple Int NodeId))
  computeVisitOrder = do
    xs <- Array.ST.empty
    flip traverseTopDown treeRef \depth id -> push (Tuple depth id) xs
    xs' <- Array.ST.unsafeFreeze xs
    pure (stableSortBy (flip compare `on` fst) xs')

push :: forall r a. a -> STArray r a -> ST r Unit
push value = void <<< Array.ST.push value

pop :: forall r a. STArray r a -> ST r (Maybe a)
pop = arraySTPopImpl Just Nothing

foreign import arraySTPopImpl :: forall h a. (a -> Maybe a) -> Maybe a -> STArray h a -> ST h (Maybe a)

-- | Perform a guaranteed-stable sort of an Array (note that
-- | `Data.Array.sort` is not guaranteed to be stable).
stableSortBy :: forall a. Ord a => (a -> a -> Ordering) -> Array a -> Array a
stableSortBy f =
  map snd <<< Array.sortBy comp <<< Array.mapWithIndex Tuple
  where
  comp :: Tuple Int a -> Tuple Int a -> Ordering
  comp (Tuple i x) (Tuple j y) =
    case f x y of
      EQ ->
        compare i j
      other ->
        other

-- | A matching of nodes in two different trees; used in the diffing algorithm.
newtype Matching
  = Matching (Map NodeId NodeId)

emptyMatching :: Matching
emptyMatching = Matching Map.empty

-- | Insert a match symmetrically; subsequent lookups of either node id will
-- | each return the other. The matching must not already contain either node
-- | id.
insertMatch :: NodeId -> NodeId -> Matching -> Matching
insertMatch x y (Matching map) =
  Matching (Map.insert x y (Map.insert y x map))

-- | Scan two diffable trees to produce a partial matching. The trees must not
-- | have overlapping node ids.
match :: forall a. Comparison a -> DiffableTree a -> DiffableTree a -> Matching
match t1 t2 = ST.run do
  m <- ST.Ref.new emptyMatching

  -- Mark all nodes of each tree 'unmatched'. We use a regular Array for the
  -- nodes of t1, since we will be matching them in bottom-up traversal order.
  -- We use an STArray for the nodes of t2, since we may match them
  -- out of order.
  unmatchedT1 <- ST.Array.unsafeThaw (allNodesBottomUp t1)
  unmatchedT2 <- allNodesBottomUp t2

  ST.Ref.read m

  where
  allNodesBottomUp tree = do
     nodes <- ST.Array.empty
     traverseBottomUp (\_ id -> { id, isLeaf: isLeaf id }) 

  go m = ?todo

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
      Tuple value []
    f =
      second (flip withMaybe (Array.insertAt k childId))
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
    f = first (const newValue)
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
            (Just <<< second (Array.delete subtreeId))
            oldParentId
        reinsertSubtree =
          Map.update
            (Just <<< second (flip withMaybe (Array.insertAt k subtreeId)))
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
