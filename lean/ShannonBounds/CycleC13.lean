/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# `G6` really is `C13^(box 6)`
-/
import ShannonBounds.BaseC13
import ShannonBounds.Defs

namespace ShannonBounds
namespace BaseC13

/-- The 13-cycle. -/
def Cyc13 : SimpleGraph (Fin 13) where
  Adj a b := (a.val + 1) % 13 = b.val ∨ (b.val + 1) % 13 = a.val
  symm := ⟨by
    intro a b h
    exact h.symm⟩
  loopless := ⟨by decide⟩

instance decCyc13 : DecidableRel Cyc13.Adj := fun a b =>
  inferInstanceAs (Decidable ((a.val + 1) % 13 = b.val ∨ (b.val + 1) % 13 = a.val))

def coord (m : Nat) (u : Code) : Fin 13 := ⟨dgt m u, dgt_lt m u⟩

lemma sconf_iff_conflict (a b : Fin 13) : sconf a.val b.val = true ↔ conflict Cyc13 a b := by
  native_decide +revert

/-- **`G6` is `C13^(box 6)`.** -/
lemma conflict_G6_iff_coords (u v : Code) :
    conflict G6 u v ↔
      (conflict Cyc13 (coord 1 u) (coord 1 v) ∧
       conflict Cyc13 (coord 13 u) (coord 13 v) ∧
       conflict Cyc13 (coord 169 u) (coord 169 v) ∧
       conflict Cyc13 (coord 2197 u) (coord 2197 v) ∧
       conflict Cyc13 (coord 28561 u) (coord 28561 v) ∧
       conflict Cyc13 (coord 371293 u) (coord 371293 v)) := by
  have key : ∀ m : Nat,
      (sconf (dgt m u) (dgt m v) = true) ↔ conflict Cyc13 (coord m u) (coord m v) :=
    fun m => sconf_iff_conflict (coord m u) (coord m v)
  rw [conflict_G6, wconf_eq]
  simp only [Bool.and_eq_true, key]
  tauto

end BaseC13
end ShannonBounds
