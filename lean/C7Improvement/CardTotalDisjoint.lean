import C7Improvement.BlockDisjoint
import C7Improvement.C4Source

namespace ShannonBounds.C7Improvement

theorem card_fold_union_le {Point : Type*} [DecidableEq Point] (sets : List (Finset Point)) :
    (sets.foldr (fun first second => first ∪ second) ∅).card ≤ (sets.map Finset.card).sum := by
  induction sets with
  | nil => simp
  | cons points sets inductionHypothesis =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left inductionHypothesis _)

theorem pairwise_disjoint_of_card_total {Point : Type*} [DecidableEq Point]
    (sets : List (Finset Point))
    (exactTotal : (sets.foldr (fun first second => first ∪ second) ∅).card =
      (sets.map Finset.card).sum) : sets.Pairwise Disjoint := by
  induction sets with
  | nil => simp
  | cons points sets inductionHypothesis =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons] at exactTotal
    have tailBound := card_fold_union_le sets
    have unionBound := Finset.card_union_le points (sets.foldr (fun first second => first ∪ second) ∅)
    have tailExact : (sets.foldr (fun first second => first ∪ second) ∅).card =
        (sets.map Finset.card).sum := by omega
    have intersectionCount := Finset.card_union_add_card_inter points
      (sets.foldr (fun first second => first ∪ second) ∅)
    have intersectionZero : (points ∩ sets.foldr (fun first second => first ∪ second) ∅).card = 0 := by
      omega
    have disjoint : Disjoint points (sets.foldr (fun first second => first ∪ second) ∅) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp intersectionZero)
    apply List.pairwise_cons.mpr
    refine ⟨?_, inductionHypothesis tailExact⟩
    intro other memberOther
    apply Finset.disjoint_left.mpr
    intro point memberPoint memberOtherPoint
    exact (Finset.disjoint_left.mp disjoint) memberPoint
      ((fold_union_member sets point).mpr ⟨other, memberOther, memberOtherPoint⟩)

end ShannonBounds.C7Improvement
