import C7Improvement.C2Geometry
import C7Improvement.BlockCountGeneral

namespace ShannonBounds.C7Improvement

open BaseC7

set_option maxRecDepth 10000
set_option maxHeartbeats 300000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 G15X J15 mainBlockLetters J15blocks
attribute [local irreducible] blockOutsideCount atom10 baseAtom

theorem mapped_sum_equal {Key : Type*} (keys : List Key) (first second : Key → ℕ)
    (equal : ∀ key ∈ keys, first key = second key) :
    (keys.map first).sum = (keys.map second).sum := by
  rw [List.map_congr_left equal]

theorem C2_block_count (letters : Letter × Letter) :
    (((G10.fam letters.1 ×ˢ BaseC7.base.fam letters.2).image transformTriple).filter outside15).card =
      blockOutsideCount (transformed10Atom letters.1) (transformed5Atom letters.2) := by
  rw [transformed_block_eq]
  exact blockOutsideCount_general _ _
    ((atom10_nodup letters.1).map transformPair_injective)
    ((baseAtom_nodup letters.2).map transformEquiv.injective)

theorem C2_sum_count : (J15blocks.map fun points => (points.filter outside15).card).sum =
    12839823 := by
  have equal : (J15blocks.map fun points => (points.filter outside15).card).sum =
      (mainBlockLetters.map fun letters =>
        blockOutsideCount (transformed10Atom letters.1) (transformed5Atom letters.2)).sum := by
    rw [J15blocks, List.map_map]
    exact mapped_sum_equal mainBlockLetters _ _ (fun letters _ => C2_block_count letters)
  exact equal.trans C2_sum_check

theorem C2_count : (J15.filter outside15).card = 12839823 := by
  calc
    _ = (J15blocks.map fun points => (points.filter outside15).card).sum := by
      rw [J15_eq_blocks]
      exact card_filter_unions J15blocks J15blocks_disjoint outside15
    _ = 12839823 := C2_sum_count

end ShannonBounds.C7Improvement
