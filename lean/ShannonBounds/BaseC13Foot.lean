/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# The footprints

`X_c` -- the words of `X` conflicting with some endpoint of the `c`-transversal -- is
itself `K`-invariant, because `X`, the ports and the endpoint maps all are and conflict is
translation invariant.  So `X_c = sigma^{-1}(SF c)` for a list `SF c` of just **six**
syndromes, and:

* `|X_c| = 169 * 6 = 1014`, by counting cosets;
* the two footprints are disjoint iff `SF0raw` and `SF1raw` are -- a `6 * 6` check
  (`sepCheck`).

Both inclusions are used for the cardinality.  `X_c subset sigma^{-1}(SF c)` is
`fp0Check`/`fp1Check`, `6 * 729` mask lookups.  The reverse uses one witness per class
(`wit0`, `wit1`): if a single word of a coset is in the footprint then, by equivariance,
all 169 are.
-/
import ShannonBounds.BaseC13Ports

namespace ShannonBounds
namespace BaseC13

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

/-- `sigma(X_c)`, six syndromes for each transversal. -/
def SFraw : Bool → List Nat
  | false => SF0raw
  | true => SF1raw

/-- the witnesses realising each footprint class -/
def witList : Bool → List (Nat × Nat)
  | false => wit0
  | true => wit1

/-- **`X_0 subset sigma^{-1}(SF0raw)`**: `6 * 729` mask lookups. -/
theorem fp0Check :
    pairRep.all (fun p => (nb (bepN false p.1)).all
      (fun w => !(memb maskSX (syn w)) || SF0raw.contains (syn w))) = true := by native_decide

/-- **`X_1 subset sigma^{-1}(SF1raw)`**, the same for the alternative transversal. -/
theorem fp1Check :
    pairRep.all (fun p => (nb (bepN true p.1)).all
      (fun w => !(memb maskSX (syn w)) || SF1raw.contains (syn w))) = true := by native_decide

/-- Every class of `SF0raw` is realised: an `X`-word conflicting with a port. -/
theorem wit0Check :
    (((wit0.map fun p => syn p.1) == SF0raw) &&
      wit0.all (fun p => (p.2 < 4826809) && wconfN p.1 (bepN false p.2) &&
        SXraw.contains (syn p.1) && SPraw.contains (syn p.2))) = true := by native_decide

theorem wit1Check :
    (((wit1.map fun p => syn p.1) == SF1raw) &&
      wit1.all (fun p => (p.2 < 4826809) && wconfN p.1 (bepN true p.2) &&
        SXraw.contains (syn p.1) && SPraw.contains (syn p.2))) = true := by native_decide

/-! ### Uniform access to the two sides -/

lemma SFbound (c : Bool) : ∀ s ∈ SFraw c, s < 28561 := by
  cases c
  · intro s hs; simpa using List.all_eq_true.mp SF0boundCheck s hs
  · intro s hs; simpa using List.all_eq_true.mp SF1boundCheck s hs

lemma SFnodup (c : Bool) : (SFraw c).Nodup := by
  cases c
  · exact nodupB_nodup SF0nodupCheck
  · exact nodupB_nodup SF1nodupCheck

lemma SFlen (c : Bool) : (SFraw c).length = 6 := by
  cases c
  · exact SF0lenCheck
  · exact SF1lenCheck

lemma fpCheck (c : Bool) :
    pairRep.all (fun p => (nb (bepN c p.1)).all
      (fun w => !(memb maskSX (syn w)) || (SFraw c).contains (syn w))) = true := by
  cases c
  · exact fp0Check
  · exact fp1Check

lemma witMap (c : Bool) : ((witList c).map fun p => syn p.1) = SFraw c := by
  cases c
  · have h := wit0Check; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1
  · have h := wit1Check; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1

lemma witProp (c : Bool) {y : Nat × Nat} (hy : y ∈ witList c) :
    y.2 < 4826809 ∧ wconfN y.1 (bepN c y.2) = true ∧
      SXraw.contains (syn y.1) = true ∧ SPraw.contains (syn y.2) = true := by
  have h : ((y.2 < 4826809) && wconfN y.1 (bepN c y.2) &&
      SXraw.contains (syn y.1) && SPraw.contains (syn y.2)) = true := by
    cases c
    · have hw := wit0Check
      simp only [Bool.and_eq_true] at hw
      exact List.all_eq_true.mp hw.2 y hy
    · have hw := wit1Check
      simp only [Bool.and_eq_true] at hw
      exact List.all_eq_true.mp hw.2 y hy
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-! ### The footprint is exactly a union of six cosets -/

/-- **`X_c subset sigma^{-1}(SF c)`.**  Translate the conflicting port back to its
representative; the same translation carries `x` into the neighbourhood tested by
`fpCheck`, and does not move its syndrome. -/
theorem syn_mem_SF {c : Bool} {x : Code} (hx : x ∈ Xset)
    (h : ∃ r ∈ portsSet, conflict G6 x (bep c r)) : syn x.val ∈ SFraw c := by
  obtain ⟨r, hr, hcon⟩ := h
  obtain ⟨p, hp, t, ht0, -, -, hep⟩ := port_descent hr
  have h1 : wconfN x.val (tadd (bepN c p.1) t) = true := by
    have h2 : wconf x (bep c r) = true := (conflict_G6 _ _).mp hcon
    rw [wconf, hep c] at h2
    exact h2
  have hwt : tadd (tsub x.val t) t = x.val := by
    rw [tadd_comm]; exact tadd_tsub x.val t x.isLt
  have h3 : wconfN (tsub x.val t) (bepN c p.1) = true := by
    have e := wconfN_tadd (tsub x.val t) (bepN c p.1) t
    rw [hwt] at e
    rw [← e]; exact h1
  have h4 : wconfN (bepN c p.1) (tsub x.val t) = true := by
    rw [wconfN_symm]; exact h3
  have hmem : tsub x.val t ∈ nb (bepN c p.1) := mem_nb _ _ (tsub_lt _ _) h4
  have hsyn : syn (tsub x.val t) = syn x.val := by
    have e := syn_tadd_ker (u := tsub x.val t) ht0
    rw [hwt] at e; exact e.symm
  have hmask : memb maskSX (syn (tsub x.val t)) = true := by
    rw [hsyn]; exact SXsub _ ((mem_Xset x).mp hx)
  have hall := List.all_eq_true.mp (List.all_eq_true.mp (fpCheck c) p hp) _ hmem
  rw [hmask] at hall
  simp only [Bool.not_true, Bool.false_or] at hall
  rw [hsyn] at hall
  exact List.contains_iff_mem.mp hall

/-- **`sigma^{-1}(SF c) subset X_c`.**  One witness per class suffices: the whole coset is
the `K`-orbit of the witness, and the port and the conflict travel with it. -/
theorem mem_foot_of_syn {c : Bool} {x : Code} (h : syn x.val ∈ SFraw c) :
    x ∈ Xset ∧ ∃ r ∈ portsSet, conflict G6 x (bep c r) := by
  rw [← witMap c] at h
  obtain ⟨y, hy, hys⟩ := List.mem_map.mp h
  obtain ⟨hy2, hyc, hyX, hyP⟩ := witProp c hy
  obtain ⟨t, -, ht0, hty⟩ := exists_ker_shift x.isLt hys.symm
  have hsx : syn x.val = syn y.1 := hys.symm
  constructor
  · rw [mem_Xset, hsx]
    exact List.contains_iff_mem.mp hyX
  · refine ⟨toCode (tadd y.2 t), ?_, ?_⟩
    · rw [mem_portsSet, toCode_val (tadd_lt _ _), syn_tadd_ker ht0]
      exact List.contains_iff_mem.mp hyP
    · rw [conflict_G6, wconf]
      show wconfN x.val (toCode (bepN c (toCode (tadd y.2 t)).val)).val = true
      rw [toCode_val (tadd_lt _ _), bepN_tadd c y.2 ht0,
        toCode_val (tadd_lt _ _), ← hty, wconfN_tadd]
      exact hyc

/-- **The footprint, both inclusions at once.** -/
theorem foot_iff (c : Bool) (x : Code) :
    (x ∈ Xset ∧ ∃ r ∈ portsSet, conflict G6 x (bep c r)) ↔ syn x.val ∈ SFraw c :=
  ⟨fun h => syn_mem_SF h.1 h.2, mem_foot_of_syn⟩

/-- **Separation**, from a `6 * 6` disjointness check. -/
theorem h_sep : ∀ x ∈ Xset, ¬ ((∃ r ∈ portsSet, conflict G6 x (bep false r)) ∧
    (∃ r ∈ portsSet, conflict G6 x (bep true r))) := by
  intro x hx hcon
  have h0 : syn x.val ∈ SF0raw := syn_mem_SF hx hcon.1
  have h1 : syn x.val ∈ SF1raw := syn_mem_SF hx hcon.2
  have h := List.all_eq_true.mp sepCheck _ h0
  rw [List.contains_iff_mem.mpr h1] at h
  exact Bool.noConfusion h

end BaseC13
end ShannonBounds
