/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# The graph of `BaseC7Data` as a strong power of the cycle graph

Two identifications:
* `G5 ≃g strongPower Cyc7 5`, via the base-7 digit expansion `finFunctionFinEquiv`;
* `Cyc7 = SimpleGraph.cycleGraph 7`.
-/
import ShannonBounds.CycleC7
import ShannonBounds.Flatten
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Circulant

namespace ShannonBounds
namespace CapC7

open BaseC7 SimpleGraph

/- The structural `DecidableEq` / `Fintype` instance *terms* exceed the default
`synthInstance.maxSize`.  They are the ordinary structural instances, merely big. -/
set_option synthInstance.maxSize 8000
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

/-- Base-7 digit expansion `Fin 16807 ≃ (Fin 5 → Fin 7)`. -/
def codeEquiv : Code ≃ (Fin 5 → Fin 7) :=
  (@finFunctionFinEquiv 7 5).symm

lemma codeEquiv_apply (u : Code) (i : Fin 5) :
    (codeEquiv u i : ℕ) = u.val / 7 ^ (i : ℕ) % 7 := rfl


/-- `codeEquiv u i` is the `coord` at modulus `7 ^ i`. -/
lemma codeEquiv_coord_pow (u : Code) (i : Fin 5) :
    codeEquiv u i = coord (7 ^ (i : ℕ)) u := by
  apply Fin.ext
  exact codeEquiv_apply u i

/-- The five coordinates of the digit expansion are the five `coord`s. -/
lemma forall_coord_iff (u v : Code) :
    (∀ i : Fin 5, conflict Cyc7 (codeEquiv u i) (codeEquiv v i)) ↔
      (conflict Cyc7 (coord 1 u) (coord 1 v) ∧ conflict Cyc7 (coord 7 u) (coord 7 v) ∧
       conflict Cyc7 (coord 49 u) (coord 49 v) ∧ conflict Cyc7 (coord 343 u) (coord 343 v) ∧
       conflict Cyc7 (coord 2401 u) (coord 2401 v)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [codeEquiv_coord_pow] using h 0
    · simpa [codeEquiv_coord_pow] using h 1
    · simpa [codeEquiv_coord_pow] using h 2
    · simpa [codeEquiv_coord_pow] using h 3
    · simpa [codeEquiv_coord_pow] using h 4
  · intro h i
    rw [codeEquiv_coord_pow u i, codeEquiv_coord_pow v i]
    fin_cases i
    · simpa using h.1
    · simpa using h.2.1
    · simpa using h.2.2.1
    · simpa using h.2.2.2.1
    · simpa using h.2.2.2.2

/-- **`G5 ≃g strongPower Cyc7 5`.** -/
def G5_iso : G5 ≃g strongPower Cyc7 5 where
  toEquiv := codeEquiv
  map_rel_iff' := by
    intro u v
    have hc : conflict (strongPower Cyc7 5) (codeEquiv u) (codeEquiv v) ↔ conflict G5 u v := by
      rw [conflict_strongPower, conflict_G5_iff_coords]
      exact forall_coord_iff u v
    constructor
    · rintro ⟨hne, h⟩
      have hne' : u ≠ v := fun huv => hne (by rw [huv])
      rcases hc.mp (Or.inr ⟨hne, h⟩) with heq | hadj
      · exact absurd heq hne'
      · exact hadj
    · rintro ⟨hne, h⟩
      rcases hc.mpr (Or.inr ⟨hne, h⟩) with heq | hadj
      · exact absurd (codeEquiv.injective heq) hne
      · exact hadj

/-- **`Cyc` is Mathlib's cycle graph.** -/
theorem Cyc_eq_cycleGraph : Cyc7 = SimpleGraph.cycleGraph 7 := by
  ext a b
  revert a b
  decide

end CapC7
end ShannonBounds
