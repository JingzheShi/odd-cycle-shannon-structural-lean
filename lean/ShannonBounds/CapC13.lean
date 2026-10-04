/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# The graph of `BaseC13Data` as a strong power of the cycle graph

Two identifications:
* `G6 ≃g strongPower Cyc13 6`, via the base-13 digit expansion `finFunctionFinEquiv`;
* `Cyc13 = SimpleGraph.cycleGraph 13`.
-/
import ShannonBounds.CycleC13
import ShannonBounds.Flatten
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Circulant

namespace ShannonBounds
namespace CapC13

open BaseC13 SimpleGraph

set_option synthInstance.maxSize 4000000
set_option synthInstance.maxHeartbeats 10000000
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- Base-13 digit expansion `Fin 4826809 ≃ (Fin 6 → Fin 13)`. -/
def codeEquiv : Code ≃ (Fin 6 → Fin 13) := (@finFunctionFinEquiv 13 6).symm

lemma codeEquiv_apply (u : Code) (i : Fin 6) :
    (codeEquiv u i : ℕ) = u.val / 13 ^ (i : ℕ) % 13 := rfl

lemma codeEquiv_coord_pow (u : Code) (i : Fin 6) :
    codeEquiv u i = coord (13 ^ (i : ℕ)) u := by
  apply Fin.ext
  exact codeEquiv_apply u i

lemma forall_coord_iff (u v : Code) :
    (∀ i : Fin 6, conflict Cyc13 (codeEquiv u i) (codeEquiv v i)) ↔
      (conflict Cyc13 (coord 1 u) (coord 1 v) ∧
       conflict Cyc13 (coord 13 u) (coord 13 v) ∧
       conflict Cyc13 (coord 169 u) (coord 169 v) ∧
       conflict Cyc13 (coord 2197 u) (coord 2197 v) ∧
       conflict Cyc13 (coord 28561 u) (coord 28561 v) ∧
       conflict Cyc13 (coord 371293 u) (coord 371293 v)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [codeEquiv_coord_pow] using h 0
    · simpa [codeEquiv_coord_pow] using h 1
    · simpa [codeEquiv_coord_pow] using h 2
    · simpa [codeEquiv_coord_pow] using h 3
    · simpa [codeEquiv_coord_pow] using h 4
    · simpa [codeEquiv_coord_pow] using h 5
  · intro h i
    rw [codeEquiv_coord_pow u i, codeEquiv_coord_pow v i]
    fin_cases i
    · simpa using h.1
    · simpa using h.2.1
    · simpa using h.2.2.1
    · simpa using h.2.2.2.1
    · simpa using h.2.2.2.2.1
    · simpa using h.2.2.2.2.2

/-- **`G6 ≃g strongPower Cyc13 6`.** -/
def G6_iso : G6 ≃g strongPower Cyc13 6 where
  toEquiv := codeEquiv
  map_rel_iff' := by
    intro u v
    have hc : conflict (strongPower Cyc13 6) (codeEquiv u) (codeEquiv v) ↔ conflict G6 u v := by
      rw [conflict_strongPower, conflict_G6_iff_coords]
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
theorem Cyc_eq_cycleGraph : Cyc13 = SimpleGraph.cycleGraph 13 := by
  ext a b
  revert a b
  decide

end CapC13
end ShannonBounds
