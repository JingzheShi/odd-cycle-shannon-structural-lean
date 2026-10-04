import C7Improvement.C4BlockCount
import C7Improvement.C4Disjoint
import C7Improvement.C4Numeric

namespace ShannonBounds.C7Improvement

attribute [local irreducible] C4source C4blocks J30 C4blockCount

theorem C4_sum_count : (C4blocks.map fun points => (points.filter outside30).card).sum =
    841760069965664 := by
  have equal : (C4blocks.map fun points => (points.filter outside30).card).sum =
      (C4source.map C4blockCount).sum := by
    rw [C4blocks, List.map_map]
    exact mapped_sum_equal C4source _ _ (fun piece _ => C4_block_count piece)
  exact equal.trans C4_sum_check

theorem C4_count : (J30.filter outside30).card = 841760069965664 := by
  calc
    _ = (C4blocks.map fun points => (points.filter outside30).card).sum := by
      rw [J30_eq_blocks]
      exact card_filter_unions C4blocks C4blocks_disjoint outside30
    _ = 841760069965664 := C4_sum_count

end ShannonBounds.C7Improvement
