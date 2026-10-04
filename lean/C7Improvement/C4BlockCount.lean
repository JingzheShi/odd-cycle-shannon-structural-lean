import C7Improvement.C4Source
import C7Improvement.C4Acceptance
import C7Improvement.C4Weights

namespace ShannonBounds.C7Improvement

open BaseC7

attribute [local irreducible] BaseC7.base G10 G10A L30 Jplus
attribute [local irreducible] neutralNear restNear inNeutral10 inRest10 aNear dNear jqIndex jnIndex
attribute [local irreducible] tenAtomList fiveAtomList

theorem C4_block_count (piece : (Fin 13 × Fin 8) × (Fin 13 × Fin 8)) :
    (((piece30Set piece).image transformThirty).filter outside30).card = C4blockCount piece := by
  rw [transformed_piece_eq]
  have equalFilter :
      ((((tenAtomList piece.1.1).map transformPair).toFinset ×ˢ
        ((fiveAtomList piece.1.2).map transform).toFinset) ×ˢ
      (((tenAtomList piece.2.1).map transformPair).toFinset ×ˢ
        ((fiveAtomList piece.2.2).map transform).toFinset)).filter outside30 =
      ((((tenAtomList piece.1.1).map transformPair).toFinset ×ˢ
        ((fiveAtomList piece.1.2).map transform).toFinset) ×ˢ
      (((tenAtomList piece.2.1).map transformPair).toFinset ×ˢ
        ((fiveAtomList piece.2.2).map transform).toFinset)).filter (fun point =>
        C4accept (mask2 (flags10 point.1.1)) (mask2 (flags5 point.1.2))
          (mask6 (right10Flags point.2.1)) (mask3 (right5Flags point.2.2)) = true) := by
    apply Finset.filter_congr
    intro point member
    exact (C4_acceptance_spec point).symm
  rw [equalFilter, four_histogram_count
    ((tenAtomList piece.1.1).map transformPair).toFinset
    ((fiveAtomList piece.1.2).map transform).toFinset
    ((tenAtomList piece.2.1).map transformPair).toFinset
    ((fiveAtomList piece.2.2).map transform).toFinset
    (fun point => mask2 (flags10 point)) (fun point => mask2 (flags5 point))
    (fun point => mask6 (right10Flags point)) (fun point => mask3 (right5Flags point)) C4accept]
  simp only [← weightL10_spec, ← weightL5_spec, ← weightR10_spec, ← weightR5_spec, C4blockCount]

end ShannonBounds.C7Improvement
