import C7Improvement.C4AtomData

namespace ShannonBounds.C7Improvement

theorem encodeFlags2_bound : ∀ flags : Fin 2 → Bool, encodeFlags flags < 4 := by native_decide
theorem encodeFlags3_bound : ∀ flags : Fin 3 → Bool, encodeFlags flags < 8 := by native_decide
theorem encodeFlags6_bound : ∀ flags : Fin 6 → Bool, encodeFlags flags < 64 := by native_decide

def mask2 (flags : Fin 2 → Bool) : Fin 4 := ⟨encodeFlags flags, encodeFlags2_bound flags⟩
def mask3 (flags : Fin 3 → Bool) : Fin 8 := ⟨encodeFlags flags, encodeFlags3_bound flags⟩
def mask6 (flags : Fin 6 → Bool) : Fin 64 := ⟨encodeFlags flags, encodeFlags6_bound flags⟩

theorem decode_mask2 (flags : Fin 2 → Bool) : decodeFlags (mask2 flags) = flags :=
  ((encodeFlags2_spec flags (mask2 flags)).mp rfl).symm
theorem decode_mask3 (flags : Fin 3 → Bool) : decodeFlags (mask3 flags) = flags :=
  ((encodeFlags3_spec flags (mask3 flags)).mp rfl).symm
theorem decode_mask6 (flags : Fin 6 → Bool) : decodeFlags (mask6 flags) = flags :=
  ((encodeFlags6_spec flags (mask6 flags)).mp rfl).symm

def tenLeftIndices : Fin 2 → Fin 13 := ![1,7]
def fiveLeftIndices : Fin 2 → Fin 8 := ![1,7]
def tenRightIndices : Fin 6 → Fin 13 := ![1,7,9,10,11,12]
def fiveRightIndices : Fin 3 → Fin 8 := ![1,2,3]

theorem C4reference_indices : ∀ reference ∈ C4reference,
    tenLeftIndices (tenLeftSlot reference.1.1) = reference.1.1 ∧
    fiveLeftIndices (fiveLeftSlot reference.1.2) = reference.1.2 ∧
    tenRightIndices (tenRightSlot reference.2.1) = reference.2.1 ∧
    fiveRightIndices (fiveRightSlot reference.2.2) = reference.2.2 := by native_decide

end ShannonBounds.C7Improvement
