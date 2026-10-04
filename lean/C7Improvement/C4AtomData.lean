import C7Improvement.C4Data

namespace ShannonBounds.C7Improvement

open BaseC7

def tenAtomSize : Fin 13 → ℕ :=
  ![129601,105709,14490,14490,5152,5152,5152,28980,134689,27488,107265,12236,16744]

theorem tenAtom_length_check : ∀ atom : Fin 13,
    (tenAtomList atom).length = tenAtomSize atom := by native_decide

theorem aNear_lookup_check : ∀ point : BaseC7.Code,
    aNear point = ((baseAtom .A).any fun witness => wconf point witness) := by native_decide

theorem dNear_lookup_check : ∀ point : BaseC7.Code,
    dNear point = ((baseAtom .D).any fun witness => wconf point witness) := by native_decide

theorem encodeFlags2_spec : ∀ flags : Fin 2 → Bool, ∀ mask : Fin 4,
    encodeFlags flags = mask.val ↔ flags = decodeFlags mask := by native_decide

theorem encodeFlags3_spec : ∀ flags : Fin 3 → Bool, ∀ mask : Fin 8,
    encodeFlags flags = mask.val ↔ flags = decodeFlags mask := by native_decide

theorem encodeFlags6_spec : ∀ flags : Fin 6 → Bool, ∀ mask : Fin 64,
    encodeFlags flags = mask.val ↔ flags = decodeFlags mask := by native_decide

end ShannonBounds.C7Improvement
