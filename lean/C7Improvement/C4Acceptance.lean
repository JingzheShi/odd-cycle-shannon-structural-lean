import C7Improvement.C4Geometry
import C7Improvement.C4Tags

namespace ShannonBounds.C7Improvement

open BaseC7

attribute [local irreducible] BaseC7.base G10 G10A G15AX G15Ahet L30 Jplus

def outside30 (point : ((BaseC7.Code × BaseC7.Code) × BaseC7.Code) ×
    ((BaseC7.Code × BaseC7.Code) × BaseC7.Code)) : Prop :=
  ¬ near (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5))
    L30.Xstar point

instance : DecidablePred outside30 := fun point =>
  inferInstanceAs (Decidable (¬ near
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5)) L30.Xstar point))

theorem near_fold_union {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (sets : List (Finset Point)) (point : Point) :
    near graph (sets.foldr (fun first second => first ∪ second) ∅) point ↔
      ∃ points ∈ sets, near graph points point := by
  induction sets with
  | nil => simp [near]
  | cons points sets inductionHypothesis =>
    simp only [List.foldr_cons, near_union, inductionHypothesis, List.mem_cons, exists_eq_or_imp]

theorem C4_acceptance_spec (point : ((BaseC7.Code × BaseC7.Code) × BaseC7.Code) ×
    ((BaseC7.Code × BaseC7.Code) × BaseC7.Code)) :
    C4accept (mask2 (flags10 point.1.1)) (mask2 (flags5 point.1.2))
      (mask6 (right10Flags point.2.1)) (mask3 (right5Flags point.2.2)) = true ↔ outside30 point := by
  rw [C4accept, List.all_eq_true]
  simp only [decode_mask2, decode_mask3, decode_mask6, bool_neg_true,
    Bool.and_eq_true]
  rw [outside30, L30_neutral_pieces, pieces30Set, near_fold_union]
  simp only [List.mem_map]
  constructor
  · intro accepted nearby
    obtain ⟨points, ⟨reference, memberReference, rfl⟩, nearby⟩ := nearby
    simp only [piece30Set, piece15Set, near_product] at nearby
    obtain ⟨left10Index, left5Index, right10Index, right5Index⟩ := C4reference_indices reference memberReference
    exact accepted reference memberReference
      ⟨⟨⟨(left10Flags_spec point.1.1 _).mpr (left10Index.symm ▸ nearby.1.1),
        (left5Flags_spec point.1.2 _).mpr (left5Index.symm ▸ nearby.1.2)⟩,
        (right10Flags_spec point.2.1 _).mpr (right10Index.symm ▸ nearby.2.1)⟩,
        (right5Flags_spec point.2.2 _).mpr (right5Index.symm ▸ nearby.2.2)⟩
  · intro outside reference memberReference flagsTrue
    apply outside
    refine ⟨piece30Set reference, ⟨reference, memberReference, rfl⟩, ?_⟩
    simp only [piece30Set, piece15Set, near_product]
    obtain ⟨left10Index, left5Index, right10Index, right5Index⟩ := C4reference_indices reference memberReference
    exact ⟨⟨left10Index ▸ (left10Flags_spec point.1.1 _).mp flagsTrue.1.1.1,
      left5Index ▸ (left5Flags_spec point.1.2 _).mp flagsTrue.1.1.2⟩,
      right10Index ▸ (right10Flags_spec point.2.1 _).mp flagsTrue.1.2,
      right5Index ▸ (right5Flags_spec point.2.2 _).mp flagsTrue.2⟩

end ShannonBounds.C7Improvement
