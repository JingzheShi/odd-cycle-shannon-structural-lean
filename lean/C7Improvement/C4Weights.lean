import C7Improvement.C4Tags
import C7Improvement.FourHistogram

namespace ShannonBounds.C7Improvement

open BaseC7

set_option maxRecDepth 10000
set_option maxHeartbeats 200000

attribute [local irreducible] neutralNear restNear inNeutral10 inRest10 aNear dNear jqIndex jnIndex
attribute [local irreducible] tenAtomList fiveAtomList

theorem encoded_frequency {Point Target Flags : Type*} [DecidableEq Point] [DecidableEq Target]
    {slots : ℕ} (points : List Point) (unique : points.Nodup) (mapping : Point → Target)
    (injective : Function.Injective mapping) (flags : Target → Flags)
    (encoding : Flags → ℕ) (masking : Flags → Fin slots)
    (correct : ∀ flag, (masking flag).val = encoding flag) (key : Fin slots) :
    frequency (points.map mapping).toFinset (fun point => masking (flags point)) key =
      (points.map fun point => encoding (flags (mapping point))).count key.val := by
  rw [list_frequency_spec (points.map mapping) (unique.map injective)]
  simp only [List.filter_map, List.length_map, List.count_eq_countP, List.countP_map,
    List.countP_eq_length_filter, Function.comp_def]
  congr 2
  funext point
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Fin.ext_iff, correct]

theorem weightL10_spec (atom : Fin 13) (key : Fin 4) :
    weightL10 atom key = frequency ((tenAtomList atom).map transformPair).toFinset
      (fun point => mask2 (flags10 point)) key := by
  simp only [weightL10, left10Weights, left10Samples, Array.getElem_ofFn]
  exact (encoded_frequency (tenAtomList atom) (tenAtom_nodup atom) transformPair
    transformPair_injective flags10 encodeFlags mask2 (fun _ => rfl) key).symm

theorem weightL5_spec (atom : Fin 8) (key : Fin 4) :
    weightL5 atom key = frequency ((fiveAtomList atom).map transform).toFinset
      (fun point => mask2 (flags5 point)) key := by
  simp only [weightL5, left5Weights, left5Samples, Array.getElem_ofFn]
  exact (encoded_frequency (fiveAtomList atom) (fiveAtom_nodup atom) transform
    transformEquiv.injective flags5 encodeFlags mask2 (fun _ => rfl) key).symm

theorem weightR10_spec (atom : Fin 13) (key : Fin 64) :
    weightR10 atom key = frequency ((tenAtomList atom).map transformPair).toFinset
      (fun point => mask6 (right10Flags point)) key := by
  simp only [weightR10, right10Weights, right10Samples, Array.getElem_ofFn]
  exact (encoded_frequency (tenAtomList atom) (tenAtom_nodup atom) transformPair
    transformPair_injective right10Flags encodeFlags mask6 (fun _ => rfl) key).symm

theorem weightR5_spec (atom : Fin 8) (key : Fin 8) :
    weightR5 atom key = frequency ((fiveAtomList atom).map transform).toFinset
      (fun point => mask3 (right5Flags point)) key := by
  simp only [weightR5, right5Weights, right5Samples, Array.getElem_ofFn]
  exact (encoded_frequency (fiveAtomList atom) (fiveAtom_nodup atom) transform
    transformEquiv.injective right5Flags encodeFlags mask3 (fun _ => rfl) key).symm

end ShannonBounds.C7Improvement
