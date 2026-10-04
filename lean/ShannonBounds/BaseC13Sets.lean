/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# `K`-cosets as the unit of data

`Fib s` is the `sigma`-fibre over the syndrome `s` -- equivalently, by `exists_ker_shift`,
the `K`-orbit of any word with that syndrome -- and `Pre Sr` is the union of the fibres
over a list of syndromes, a `K`-invariant subset of `C13^(box 6)`.  `I` and `X` are
`Pre Sraw` and `Pre SXraw`; this file computes their cardinalities (`169 * 370 = 62530`)
by counting cosets and proves them independent via `indep_of_syn_gen`.
-/
import ShannonBounds.BaseC13Data

namespace ShannonBounds
namespace BaseC13

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

/-! ### Fibres -/

/-- The `sigma`-fibre over `s`, i.e. the `K`-orbit of any word of syndrome `s`. -/
def Fib (s : Nat) : Finset Code := (Finset.range 169).image (fun k => toCode (enc s k))

lemma mem_Fib {s : Nat} (hs : s < 28561) (u : Code) : u ∈ Fib s ↔ syn u.val = s := by
  constructor
  · intro h
    obtain ⟨k, -, hku⟩ := Finset.mem_image.mp h
    rw [← hku]
    show syn ((toCode (enc s k)).val) = s
    rw [toCode_val (enc_lt s k), syn_enc hs]
  · intro h
    refine Finset.mem_image.mpr ⟨kap u.val, Finset.mem_range.mpr (kap_lt _), ?_⟩
    rw [← h, enc_syn_kap u.isLt, toCode_self]

/-- **Every fibre has exactly `|K| = 169` elements.** -/
lemma card_Fib (s : Nat) : (Fib s).card = 169 := by
  rw [Fib, Finset.card_image_of_injOn, Finset.card_range]
  intro k1 h1 k2 h2 he
  have e1 := congrArg Fin.val he
  rw [toCode_val (enc_lt s k1), toCode_val (enc_lt s k2)] at e1
  rw [← kap_enc s (Finset.mem_range.mp h1), ← kap_enc s (Finset.mem_range.mp h2), e1]

lemma disjoint_Fib {s s' : Nat} (hs : s < 28561) (hs' : s' < 28561) (h : s ≠ s') :
    Disjoint (Fib s) (Fib s') := by
  rw [Finset.disjoint_left]
  intro u h1 h2
  exact h (((mem_Fib hs u).mp h1).symm.trans ((mem_Fib hs' u).mp h2))

/-- The union of the fibres over a list of syndromes. -/
def Pre (Sr : List Nat) : Finset Code := Sr.toFinset.biUnion Fib

lemma mem_Pre {Sr : List Nat} (hb : ∀ s ∈ Sr, s < 28561) (u : Code) :
    u ∈ Pre Sr ↔ syn u.val ∈ Sr := by
  rw [Pre, Finset.mem_biUnion]
  constructor
  · rintro ⟨s, hs, hu⟩
    rw [List.mem_toFinset] at hs
    rw [(mem_Fib (hb s hs) u).mp hu]
    exact hs
  · intro h
    exact ⟨syn u.val, List.mem_toFinset.mpr h, (mem_Fib (hb _ h) u).mpr rfl⟩

/-- **`|sigma^{-1}(Sr)| = 169 * |Sr|`.**  Cardinality by counting cosets. -/
lemma card_Pre {Sr : List Nat} (hb : ∀ s ∈ Sr, s < 28561) (hn : Sr.Nodup) :
    (Pre Sr).card = 169 * Sr.length := by
  rw [Pre, Finset.card_biUnion, Finset.sum_congr rfl (fun s _ => card_Fib s),
    Finset.sum_const, smul_eq_mul, List.toFinset_card_of_nodup hn, Nat.mul_comm]
  intro s hs s' hs' hne
  exact disjoint_Fib (hb s (List.mem_toFinset.mp hs)) (hb s' (List.mem_toFinset.mp hs')) hne

/-! ### Independence of a union of cosets -/

theorem indepPre {Sr : List Nat} (hb : ∀ s ∈ Sr, s < 28561) (mem : Nat → Bool)
    (hsub : ∀ s ∈ Sr, mem s = true)
    (hind : ∀ s ∈ Sr, ∀ e ∈ Delta, mem (addSyn s e) = false) :
    G6.IsIndepSet ((Pre Sr : Finset Code) : Set Code) := by
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, mem_Pre hb] at hx hy
  have hw : wconfN x.val y.val = true := hadj.2
  have hc := indep_of_syn_gen mem hsub hind x.isLt y.isLt hx hy
    (fun he => hne (Fin.val_injective he).symm)
  rw [hw] at hc
  exact Bool.noConfusion hc

/-! ### The two independent sets -/

lemma Sbound : ∀ s ∈ Sraw, s < 28561 := by
  intro s hs; simpa using List.all_eq_true.mp SboundCheck s hs

lemma SXbound : ∀ s ∈ SXraw, s < 28561 := by
  intro s hs; simpa using List.all_eq_true.mp SXboundCheck s hs

lemma Snodup : Sraw.Nodup := ssorted_nodup SsortCheck
lemma SXnodup : SXraw.Nodup := ssorted_nodup SXsortCheck

lemma Ssub : ∀ s ∈ Sraw, memb maskS s = true :=
  fun s hs => List.all_eq_true.mp SsubCheck s hs

lemma SXsub : ∀ s ∈ SXraw, memb maskSX s = true :=
  fun s hs => List.all_eq_true.mp SXsubCheck s hs

lemma Sind : ∀ s ∈ Sraw, ∀ e ∈ Delta, memb maskS (addSyn s e) = false := by
  intro s hs e he
  simpa using List.all_eq_true.mp (List.all_eq_true.mp SindCheck s hs) e he

lemma SXind : ∀ s ∈ SXraw, ∀ e ∈ Delta, memb maskSX (addSyn s e) = false := by
  intro s hs e he
  simpa using List.all_eq_true.mp (List.all_eq_true.mp SXindCheck s hs) e he

/-- The base independent set `I = sigma^{-1}(S)`, `|I| = 169 * 370 = 62530`. -/
def Iset : Finset Code := Pre Sraw

/-- The auxiliary code `X = sigma^{-1}(S_X)`. -/
def Xset : Finset Code := Pre SXraw

lemma mem_Iset (u : Code) : u ∈ Iset ↔ syn u.val ∈ Sraw := mem_Pre Sbound u
lemma mem_Xset (u : Code) : u ∈ Xset ↔ syn u.val ∈ SXraw := mem_Pre SXbound u

theorem Icard : Iset.card = 62530 := by
  rw [Iset, card_Pre Sbound Snodup, SlenCheck]

theorem Xcard : Xset.card = 62530 := by
  rw [Xset, card_Pre SXbound SXnodup, SXlenCheck]

theorem isIndepSet_I : G6.IsIndepSet (Iset : Set Code) :=
  indepPre Sbound (memb maskS) Ssub Sind

theorem isIndepSet_X : G6.IsIndepSet (Xset : Set Code) :=
  indepPre SXbound (memb maskSX) SXsub SXind

/-! ### `K` really is the group generated by the two stated generators

`kerList` is `{a*g1 + b*g2}` in closed form.  Its 169 elements are distinct and all lie in
`ker sigma`, and `ker sigma = Fib 0` has exactly 169 elements -- so the span is all of
`ker sigma`.  `ker_span_eq` records that equality. -/

theorem kerBoundCheck : kerList.all (fun u => u < 4826809) = true := by native_decide

theorem ker_span_eq : (kerList.map toCode).toFinset = Fib 0 := by
  have hb : ∀ u ∈ kerList, u < 4826809 := by
    intro u hu; simpa using List.all_eq_true.mp kerBoundCheck u hu
  have hz : ∀ u ∈ kerList, syn u = 0 := by
    intro u hu
    have h := kerGenCheck
    simp only [Bool.and_eq_true] at h
    simpa using List.all_eq_true.mp h.2 u hu
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact (mem_Fib (by decide) _).mpr (by rw [toCode_val (hb u hu)]; exact hz u hu)
  · rw [card_Fib]
    have hnd : (kerList.map toCode).Nodup := by
      refine List.Nodup.map_on ?_ (nodupB_nodup kerListNodup)
      intro a ha b hb' hab
      have hv := congrArg Fin.val hab
      rwa [toCode_val (hb a ha), toCode_val (hb b hb')] at hv
    rw [List.toFinset_card_of_nodup hnd, List.length_map, kerListLen]

end BaseC13
end ShannonBounds
