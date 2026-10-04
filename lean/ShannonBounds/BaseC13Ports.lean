/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# Ports, alternatives, and the `K`-descent

The 1014 ports are `sigma^{-1}(SPraw)`, six full `K`-cosets, and the pairing
`parent -> alternative` is `K`-equivariant: within a coset the alternative is always the
parent shifted by one fixed translation `tvec`.  `port_descent` packages this: *every*
port is `p.1 + t` for one of the six representatives `p` and some `t` in `K`, and then
*both* endpoints of that port are the representative's endpoints shifted by the same `t`.

Every structure field below is discharged from `port_descent` plus a six-entry table
lookup.
-/
import ShannonBounds.BaseC13Sets

namespace ShannonBounds
namespace BaseC13

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

/-! ### The two transversals as unions of cosets -/

lemma SPbound : ∀ s ∈ SPraw, s < 28561 := by
  intro s hs; simpa using List.all_eq_true.mp SPboundCheck s hs

lemma SAbound : ∀ s ∈ SAraw, s < 28561 := by
  intro s hs; simpa using List.all_eq_true.mp SAboundCheck s hs

lemma SPnodup : SPraw.Nodup := nodupB_nodup SPnodupCheck
lemma SAnodup : SAraw.Nodup := nodupB_nodup SAnodupCheck

/-- The parents, `P_0 = sigma^{-1}(S_P)`; `|ports| = 169 * 6 = 1014`. -/
def portsSet : Finset Code := Pre SPraw

lemma mem_portsSet (r : Code) : r ∈ portsSet ↔ syn r.val ∈ SPraw := mem_Pre SPbound r

theorem portsCard : portsSet.card = 1014 := by
  rw [portsSet, card_Pre SPbound SPnodup, SPlenCheck]

/-! ### The endpoint maps

`bside` is false for every listed port, as `sidesCheck` below records. -/

def bside (_ : Code) : Bool := false

def bepN : Bool → Nat → Nat
  | false, r => r
  | true, r => tadd r (tvec (syn r))

def bep (c : Bool) (r : Code) : Code := toCode (bepN c r.val)

theorem bepN_lt (c : Bool) {r : Nat} (hr : r < 4826809) : bepN c r < 4826809 := by
  cases c
  · exact hr
  · exact tadd_lt _ _

/-- **The endpoint maps commute with the `K`-action.**  This is the equivariance of the
port structure, and it is what makes the descent work. -/
theorem bepN_tadd (c : Bool) (r : Nat) {t : Nat} (ht : syn t = 0) :
    bepN c (tadd r t) = tadd (bepN c r) t := by
  cases c
  · rfl
  · show tadd (tadd r t) (tvec (syn (tadd r t))) = tadd (tadd r (tvec (syn r))) t
    rw [syn_tadd_ker ht]
    exact tadd_swap r (tvec (syn r)) t

lemma bep_false (r : Code) : bep false r = r := by
  show toCode r.val = r
  exact toCode_self r

lemma bside_not (r : Code) : (!bside r) = true := rfl

/-- Each representative's `true`-endpoint is its recorded alternative. -/
lemma bepN_rep {p : Nat × Nat} (hp : p ∈ pairRep) : bepN true p.1 = p.2 := by
  have h := List.all_eq_true.mp tvecCheck p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show tadd p.1 (tvec (syn p.1)) = p.2
  exact h.2

lemma repBound {p : Nat × Nat} (hp : p ∈ pairRep) : p.1 < 4826809 ∧ p.2 < 4826809 := by
  have h := List.all_eq_true.mp repBoundCheck p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

lemma repSynP : (pairRep.map fun p => syn p.1) = SPraw := by
  have h := repSynCheck
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

lemma repSynA : (pairRep.map fun p => syn p.2) = SAraw := by
  have h := repSynCheck
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-! ### The descent -/

/-- **Every port is a `K`-translate of one of the six representatives, and both of its
endpoints are that representative's endpoints under the same translate.** -/
theorem port_descent {r : Code} (hr : r ∈ portsSet) :
    ∃ p ∈ pairRep, ∃ t, syn t = 0 ∧ t < 4826809 ∧ tadd p.1 t = r.val ∧
      ∀ c : Bool, (bep c r).val = tadd (bepN c p.1) t := by
  have hs : syn r.val ∈ SPraw := (mem_portsSet r).mp hr
  rw [← repSynP] at hs
  obtain ⟨p, hp, hps⟩ := List.mem_map.mp hs
  obtain ⟨hp1, -⟩ := repBound hp
  obtain ⟨t, htN, ht0, htr⟩ := exists_ker_shift r.isLt hps.symm
  refine ⟨p, hp, t, ht0, htN, htr, fun c => ?_⟩
  show (toCode (bepN c r.val)).val = _
  rw [← htr, bepN_tadd c p.1 ht0, toCode_val (tadd_lt _ _)]

/-- The alternative of any port lies in `sigma^{-1}(S_A)`. -/
theorem bep_true_mem_alt {r : Code} (hr : r ∈ portsSet) : bep true r ∈ Pre SAraw := by
  obtain ⟨p, hp, t, ht0, -, -, hep⟩ := port_descent hr
  rw [mem_Pre SAbound, hep true, syn_tadd_ker ht0, bepN_rep hp, ← repSynA]
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

/-! ### The structure fields -/

/-- **`P_0 subset I`**, from six coset memberships. -/
theorem h_ports : portsSet ⊆ Iset := by
  intro r hr
  rw [mem_Iset]
  have hs := (mem_portsSet r).mp hr
  exact List.contains_iff_mem.mp (List.all_eq_true.mp SPinSCheck _ hs)

theorem h_ep_parent : ∀ r ∈ portsSet, bep (bside r) r = r := fun r _ => bep_false r

/-- **The alternative leaves `I`**, from six coset non-memberships. -/
theorem h_alt_not : ∀ r ∈ portsSet, bep (!bside r) r ∉ Iset := by
  intro r hr hcon
  rw [bside_not, mem_Iset] at hcon
  obtain ⟨p, hp, t, ht0, -, -, hep⟩ := port_descent hr
  rw [hep true, syn_tadd_ker ht0, bepN_rep hp] at hcon
  have hmem : syn p.2 ∈ SAraw := by
    rw [← repSynA]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have h := List.all_eq_true.mp SAnotSCheck _ hmem
  rw [List.contains_iff_mem.mpr hcon] at h
  exact Bool.noConfusion h

/-- **The pairs are edges**: every port conflicts with its own alternative.  Six
representative checks (`pairConflict`) plus the descent: a port is `p.1 + t` and its
alternative is `p.2 + t` for the same `t ∈ K`, and conflict is translation invariant
(`wconfN_tadd`).  With `h_private` this makes `N[alt r] ∩ I = {r}` an equality. -/
theorem h_ep_conflict : ∀ r ∈ portsSet, conflict G6 r (bep (!bside r) r) := by
  intro r hr
  rw [bside_not, conflict_G6]
  obtain ⟨p, hp, t, ht0, -, htr, hep⟩ := port_descent hr
  show wconfN r.val (bep true r).val = true
  rw [hep true, bepN_rep hp, ← htr, wconfN_tadd]
  simpa using List.all_eq_true.mp pairConflict p hp

/-- **Distinct ports have distinct alternatives.**  The six alternative cosets are
distinct (`SAnodupCheck`), which pins down the orbit; translation is injective, which
pins down the port inside it. -/
theorem h_alt_inj : ∀ r ∈ portsSet, ∀ s ∈ portsSet,
    bep (!bside r) r = bep (!bside s) s → r = s := by
  intro r hr s hs hrs
  rw [bside_not, bside_not] at hrs
  obtain ⟨p, hp, t, ht0, htN, htr, hep⟩ := port_descent hr
  obtain ⟨q, hq, t', ht0', htN', htr', hep'⟩ := port_descent hs
  have hval : tadd p.2 t = tadd q.2 t' := by
    have h1 := congrArg Fin.val hrs
    rwa [hep true, hep' true, bepN_rep hp, bepN_rep hq] at h1
  -- the two alternatives lie in the same coset, so they come from the same representative
  have hsyn : syn p.2 = syn q.2 := by
    have := congrArg syn hval
    rwa [syn_tadd_ker ht0, syn_tadd_ker ht0'] at this
  have hnd : (pairRep.map fun p => syn p.2).Nodup := by rw [repSynA]; exact SAnodup
  have hpq : p = q := List.inj_on_of_nodup_map hnd hp hq hsyn
  subst hpq
  -- same representative: translation is injective, so the translates agree
  obtain ⟨-, hp2⟩ := repBound hp
  have htt : t = t' := by
    refine tadd_cancel (t := p.2) htN htN' ?_
    rw [tadd_comm t p.2, tadd_comm t' p.2]
    exact hval
  apply Fin.val_injective
  rw [← htr, ← htr', htt]

end BaseC13
end ShannonBounds
