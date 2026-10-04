import C7Improvement.Flags15
import C7Improvement.SparseCount

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem
open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 G15X neutralNear restNear inNeutral10 inRest10

theorem blockOutsideCount_spec (points : List (BaseC7.Code × BaseC7.Code)) (unique : points.Nodup)
    (letter : Letter) :
    ((points.toFinset ×ˢ BaseC7.base.fam letter).filter fun point =>
      ¬ near (strongProd (strongProd G5 G5) G5) G15X.Xstar point).card =
      blockOutsideCount points (baseAtom letter) := by
  rw [← baseAtom_eq letter, ← ref15_eq,
    count_outside_product_on points.toFinset (baseAtom letter).toFinset ref15Left ref15Right
      Finset.univ Finset.univ (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)]
  unfold blockOutsideCount weight10 weight5
  rw [← flags10_eq, ← flags5_eq]
  apply Finset.sum_congr rfl
  intro leftFlags memberLeft
  apply Finset.sum_congr rfl
  intro rightFlags memberRight
  simp only [bool_neg_true, Bool.eq_false_iff, mergeFlags]
  rw [list_frequency_spec points unique flags10 leftFlags,
    list_frequency_spec (baseAtom letter) (baseAtom_nodup letter) flags5 rightFlags]
  simp only [Bool.decide_eq_true, bool_neg_true]

end ShannonBounds.C7Improvement
