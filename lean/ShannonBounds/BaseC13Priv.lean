/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# Privacy, on six representatives

`privCheck` says: of the 729 cyclic neighbours of each of the **six** representative
alternatives, the only one whose syndrome the mask accepts is that representative's own
parent.  `6 * 729` lookups.

The descent is `port_descent` plus `wconfN_tadd`: a port `r` is `p.1 + t` with `t` in `K`,
so its alternative is `p.2 + t`; translating a conflicting `I`-word `w` back by `t` keeps
it in `I` (because `I` is a union of `K`-cosets and `sigma(t) = 0`) and keeps the conflict
(because conflict is translation invariant), so `privCheck` applies to `w - t`.
-/
import ShannonBounds.BaseC13Ports

namespace ShannonBounds
namespace BaseC13

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

/-- **Privacy on the six orbit representatives**: `6 * 729` mask lookups. -/
theorem privCheck :
    pairRep.all (fun p => (nb p.2).all
      (fun w => !(memb maskS (syn w)) || (w == p.1))) = true := by native_decide

theorem h_private : ∀ r ∈ portsSet, ∀ w ∈ Iset,
    conflict G6 (bep (!bside r) r) w → w = r := by
  intro r hr w hw hc
  rw [bside_not] at hc
  obtain ⟨p, hp, t, ht0, -, htr, hep⟩ := port_descent hr
  have h1 : wconfN (tadd p.2 t) w.val = true := by
    have h2 : wconf (bep true r) w = true := (conflict_G6 _ _).mp hc
    rw [wconf, hep true, bepN_rep hp] at h2
    exact h2
  -- pull `w` back along the same translation
  have hwt : tadd (tsub w.val t) t = w.val := by
    rw [tadd_comm]; exact tadd_tsub w.val t w.isLt
  have h3 : wconfN p.2 (tsub w.val t) = true := by
    have e := wconfN_tadd p.2 (tsub w.val t) t
    rw [hwt] at e
    rw [← e]; exact h1
  have hmem : tsub w.val t ∈ nb p.2 := mem_nb _ _ (tsub_lt _ _) h3
  have hsyn : syn (tsub w.val t) = syn w.val := by
    have e := syn_tadd_ker (u := tsub w.val t) ht0
    rw [hwt] at e; exact e.symm
  have hmask : memb maskS (syn (tsub w.val t)) = true := by
    rw [hsyn]; exact Ssub _ ((mem_Iset w).mp hw)
  have hall := List.all_eq_true.mp (List.all_eq_true.mp privCheck p hp) _ hmem
  rw [hmask] at hall
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hall
  apply Fin.val_injective
  rw [← hwt, hall, htr]

end BaseC13
end ShannonBounds
