
exports.arraySTPopImpl = function arraySTPopImpl(just) {
  return function(nothing) {
    return function(array) {
      return function() {
        return xs.length === 0 ? nothing : just(xs.pop());
      }
    }
  }
}
