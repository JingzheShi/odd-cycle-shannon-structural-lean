/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# `G5` really is `C7^(box 5)`

`BaseC7.G5` is defined by a `Bool`-valued conflict test on base-7 codes, chosen so
that `native_decide` can evaluate it.  This file exhibits the 7-cycle `Cyc7` explicitly
and proves that the test is exactly conflict in `C7`, coordinatewise, so that `G5`
is the strong 5th power of the 7-cycle.
-/
import ShannonBounds.BaseC7
import ShannonBounds.Defs

namespace ShannonBounds
namespace BaseC7

/-- The 7-cycle `C7`: `a` and `b` are adjacent iff they differ by one, cyclically. -/
def Cyc7 : SimpleGraph (Fin 7) where
  Adj a b := (a.val + 1) % 7 = b.val ∨ (b.val + 1) % 7 = a.val
  symm := ⟨by
    intro a b h
    exact h.symm⟩
  loopless := ⟨by decide⟩

instance decCyc7 : DecidableRel Cyc7.Adj := fun a b =>
  inferInstanceAs (Decidable ((a.val + 1) % 7 = b.val ∨ (b.val + 1) % 7 = a.val))

/-- Coordinate `k` of a code, as an element of `Fin 7`. -/
def coord (m : Nat) (u : Code) : Fin 7 := ⟨dgt m u, dgt_lt m u⟩

/-- The `Bool` test `sconf` is exactly conflict in the 7-cycle. -/
lemma sconf_iff_conflict (a b : Fin 7) : sconf a.val b.val = true ↔ conflict Cyc7 a b := by
  native_decide +revert

/-- **`G5` is `C7^(box 5)`.**  Conflict in `G5` is conflict in *every* one of the five
`C7`-coordinates, which is the defining property of the strong 5th power. -/
lemma conflict_G5_iff_coords (u v : Code) :
    conflict G5 u v ↔
      (conflict Cyc7 (coord 1 u) (coord 1 v) ∧ conflict Cyc7 (coord 7 u) (coord 7 v) ∧
       conflict Cyc7 (coord 49 u) (coord 49 v) ∧ conflict Cyc7 (coord 343 u) (coord 343 v) ∧
       conflict Cyc7 (coord 2401 u) (coord 2401 v)) := by
  have key : ∀ m : Nat,
      (sconf (dgt m u) (dgt m v) = true) ↔ conflict Cyc7 (coord m u) (coord m v) :=
    fun m => sconf_iff_conflict (coord m u) (coord m v)
  rw [conflict_G5, wconf]
  simp only [Bool.and_eq_true, key]
  tauto

/-- The adjacency form of the same statement. -/
lemma adj_G5_iff_coords (u v : Code) :
    G5.Adj u v ↔ u ≠ v ∧
      (conflict Cyc7 (coord 1 u) (coord 1 v) ∧ conflict Cyc7 (coord 7 u) (coord 7 v) ∧
       conflict Cyc7 (coord 49 u) (coord 49 v) ∧ conflict Cyc7 (coord 343 u) (coord 343 v) ∧
       conflict Cyc7 (coord 2401 u) (coord 2401 v)) := by
  constructor
  · intro h
    exact ⟨h.1, (conflict_G5_iff_coords u v).mp (Or.inr h)⟩
  · intro ⟨hne, h⟩
    rcases (conflict_G5_iff_coords u v).mpr h with he | h'
    · exact absurd he hne
    · exact h'

end BaseC7


end ShannonBounds
