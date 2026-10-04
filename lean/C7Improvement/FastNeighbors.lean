import C7Improvement.PackedNeighborhood
import ShannonBounds.CapC7

namespace ShannonBounds.C7Improvement

open BaseC7

def neighbors7 (point : Fin 7) : List (Fin 7) :=
  [⟨(point.val + 6) % 7, Nat.mod_lt _ (by decide)⟩, point,
    ⟨(point.val + 1) % 7, Nat.mod_lt _ (by decide)⟩]

theorem neighbors7_spec : ∀ point neighbor : Fin 7,
    neighbor ∈ neighbors7 point ↔ sconf point.val neighbor.val = true := by
  native_decide

def encodedProduct5 (first second third fourth fifth : List (Fin 7)) : List BaseC7.Code :=
  first.flatMap fun digit0 => second.flatMap fun digit1 => third.flatMap fun digit2 =>
    fourth.flatMap fun digit3 => fifth.map fun digit4 =>
      CapC7.codeEquiv.symm ![digit0, digit1, digit2, digit3, digit4]

theorem encodedProduct5_spec (first second third fourth fifth : List (Fin 7))
    (point : BaseC7.Code) : point ∈ encodedProduct5 first second third fourth fifth ↔
      CapC7.codeEquiv point 0 ∈ first ∧ CapC7.codeEquiv point 1 ∈ second ∧
      CapC7.codeEquiv point 2 ∈ third ∧ CapC7.codeEquiv point 3 ∈ fourth ∧
      CapC7.codeEquiv point 4 ∈ fifth := by
  simp only [encodedProduct5, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨digit0, member0, digit1, member1, digit2, member2,
      digit3, member3, digit4, member4, rfl⟩
    simp only [CapC7.codeEquiv.apply_symm_apply]
    exact ⟨member0, member1, member2, member3, member4⟩
  · rintro ⟨member0, member1, member2, member3, member4⟩
    refine ⟨_, member0, _, member1, _, member2, _, member3, _, member4, ?_⟩
    apply CapC7.codeEquiv.injective
    rw [CapC7.codeEquiv.apply_symm_apply]
    funext index
    fin_cases index <;> rfl

def fastNeighbors5 (point : BaseC7.Code) : List BaseC7.Code :=
  encodedProduct5 (neighbors7 (CapC7.codeEquiv point 0)) (neighbors7 (CapC7.codeEquiv point 1))
    (neighbors7 (CapC7.codeEquiv point 2)) (neighbors7 (CapC7.codeEquiv point 3))
    (neighbors7 (CapC7.codeEquiv point 4))

theorem fastNeighbors5_spec (point neighbor : BaseC7.Code) :
    neighbor ∈ fastNeighbors5 point ↔ conflict G5 point neighbor := by
  rw [fastNeighbors5, encodedProduct5_spec, conflict_G5]
  simp only [neighbors7_spec, CapC7.codeEquiv_apply, wconf, dgt, Bool.and_eq_true]
  tauto

theorem packedNear_fast_spec (points : List (BaseC7.Code × BaseC7.Code))
    (point : BaseC7.Code × BaseC7.Code) :
    packedNear fastNeighbors5 points point = true ↔ near (strongProd G5 G5) points.toFinset point := by
  rw [packedNear_spec]
  simp only [fastNeighbors5_spec, near, List.mem_toFinset, conflict_strongProd_iff]
  constructor
  · rintro ⟨first, firstConflict, second, secondConflict, member⟩
    exact ⟨(first, second), member, firstConflict, secondConflict⟩
  · rintro ⟨witness, member, firstConflict, secondConflict⟩
    exact ⟨witness.1, firstConflict, witness.2, secondConflict, member⟩

end ShannonBounds.C7Improvement
