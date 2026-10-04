import C7Improvement.BlockCountOutside

namespace ShannonBounds.C7Improvement

open BaseC7
open scoped BigOperators

attribute [local irreducible] BaseC7.base G10 G15X neutralNear restNear inNeutral10 inRest10

theorem blockOutsideCount_general (left : List (BaseC7.Code × BaseC7.Code))
    (right : List BaseC7.Code) (leftUnique : left.Nodup) (rightUnique : right.Nodup) :
    ((left.toFinset ×ˢ right.toFinset).filter outside15).card =
      blockOutsideCount left right := by
  change ((left.toFinset ×ˢ right.toFinset).filter fun point =>
    ¬ near (strongProd (strongProd G5 G5) G5) G15X.Xstar point).card = _
  rw [← ref15_eq, count_outside_product_on left.toFinset right.toFinset ref15Left ref15Right
    Finset.univ Finset.univ (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)]
  unfold blockOutsideCount weight10 weight5
  rw [← flags10_eq, ← flags5_eq]
  apply Finset.sum_congr rfl
  intro leftFlags memberLeft
  apply Finset.sum_congr rfl
  intro rightFlags memberRight
  simp only [bool_neg_true, Bool.eq_false_iff, mergeFlags]
  rw [list_frequency_spec left leftUnique flags10 leftFlags,
    list_frequency_spec right rightUnique flags5 rightFlags]
  simp only [Bool.decide_eq_true]

end ShannonBounds.C7Improvement
