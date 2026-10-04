/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# The base `RichPortSystem` on `C7^(box 5)`

All finite certificates in this assembly are computations on the literal data
lists.  In particular, no `decide` below is applied to a proposition of the
form `∀ r ∈ portsSet, ...`: such a proposition is a guarded universal over all
`Code = Fin 16807`, not an eight-element fold.
-/
import ShannonBounds.BaseC7Data

namespace ShannonBounds
namespace BaseC7

set_option maxHeartbeats 1000000

/-! ### Membership in the data `Finset`s is `List` membership -/

lemma mem_portsSet (r : Code) : r ∈ portsSet ↔ r ∈ portsList := by
  rw [portsSet, Finset.mem_mk, Multiset.mem_coe]

lemma mem_Iset (x : Code) : x ∈ Iset ↔ x ∈ Ilist := by
  rw [Iset, Finset.mem_mk, Multiset.mem_coe]

lemma mem_Xset (x : Code) : x ∈ Xset ↔ x ∈ Xlist := by
  rw [Xset, Finset.mem_mk, Multiset.mem_coe]

/-! ### The footprint predicate as a `Bool` computation -/

/-- Does `x` conflict with some `P c`-endpoint? -/
def fpB (c : Bool) (x : Code) : Bool :=
  portsList.any fun r => wconf x (bep c r)

/-- The bridge from the eight-element computation to the structure's `Prop`. -/
lemma fpB_iff (c : Bool) (x : Code) :
    (∃ r ∈ portsSet, conflict G5 x (bep c r)) ↔ fpB c x = true := by
  rw [fpB, List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hc⟩
    exact ⟨r, (mem_portsSet r).mp hr, (conflict_G5 _ _).mp hc⟩
  · rintro ⟨r, hr, hc⟩
    exact ⟨r, (mem_portsSet r).mpr hr, (conflict_G5 _ _).mpr hc⟩

/-! ### Raw certificates for the structure fields -/

/-- Every listed port occurs in the literal independent-set list. -/
theorem portsCheck :
    portsList.all (fun r => Ilist.contains r) = true := by
  native_decide

theorem h_ports : portsSet ⊆ Iset := by
  intro r hr
  rw [mem_Iset]
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp portsCheck r ((mem_portsSet r).mp hr))

/-- The selected endpoint of each listed pair is its parent. -/
theorem epParentCheck :
    portsList.all (fun r => bep (bside r) r == r) = true := by
  native_decide

theorem h_ep_parent : ∀ r ∈ portsSet, bep (bside r) r = r := by
  intro r hr
  have h := List.all_eq_true.mp epParentCheck r ((mem_portsSet r).mp hr)
  simpa using h

/-- The alternative endpoint of each listed pair is absent from `Ilist`. -/
theorem altNotCheck :
    portsList.all (fun r => !(Ilist.contains (bep (!bside r) r))) = true := by
  native_decide

theorem h_alt_not : ∀ r ∈ portsSet, bep (!bside r) r ∉ Iset := by
  intro r hr
  have h := List.all_eq_true.mp altNotCheck r ((mem_portsSet r).mp hr)
  rw [mem_Iset, ← List.contains_iff_mem]
  simpa using h

/-- Equality of two listed alternatives implies equality of their parents. -/
theorem altInjCheck :
    portsList.all (fun r => portsList.all (fun s =>
      !(bep (!bside r) r == bep (!bside s) s) || (r == s))) = true := by
  native_decide

theorem h_alt_inj : ∀ r ∈ portsSet, ∀ s ∈ portsSet,
    bep (!bside r) r = bep (!bside s) s → r = s := by
  intro r hr s hs hrs
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp altInjCheck r ((mem_portsSet r).mp hr))
    s ((mem_portsSet s).mp hs)
  simpa [hrs] using h

/-- The false transversal is independent on the literal eight-element list. -/
theorem pFalseCheck :
    portsList.all (fun r => portsList.all (fun s =>
      (r == s) || !(wconf (bep false r) (bep false s)))) = true := by
  native_decide

/-- The true transversal is independent on the literal eight-element list. -/
theorem pTrueCheck :
    portsList.all (fun r => portsList.all (fun s =>
      (r == s) || !(wconf (bep true r) (bep true s)))) = true := by
  native_decide

theorem h_P_indep : ∀ c : Bool, ∀ r ∈ portsSet, ∀ s ∈ portsSet, r ≠ s →
    ¬ conflict G5 (bep c r) (bep c s) := by
  intro c r hr s hs hrs hc
  cases c with
  | false =>
      have h := List.all_eq_true.mp
        (List.all_eq_true.mp pFalseCheck r ((mem_portsSet r).mp hr))
        s ((mem_portsSet s).mp hs)
      rw [(conflict_G5 _ _).mp hc] at h
      simp [hrs] at h
  | true =>
      have h := List.all_eq_true.mp
        (List.all_eq_true.mp pTrueCheck r ((mem_portsSet r).mp hr))
        s ((mem_portsSet s).mp hs)
      rw [(conflict_G5 _ _).mp hc] at h
      simp [hrs] at h

/-- Privacy on the literal `8 × 367` input. -/
theorem privCheck :
    portsList.all (fun r => Ilist.all
      (fun w => !(wconf (bep (!bside r) r) w) || (w == r))) = true := by
  native_decide

theorem h_private : ∀ r ∈ portsSet, ∀ w ∈ Iset,
    conflict G5 (bep (!bside r) r) w → w = r := by
  intro r hr w hw hc
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp privCheck r ((mem_portsSet r).mp hr))
    w ((mem_Iset w).mp hw)
  rw [(conflict_G5 _ _).mp hc] at h
  simpa using h

/-- Separation on the literal `367 × 2 × 8` input. -/
theorem sepCheck :
    Xlist.all (fun x => !(fpB false x && fpB true x)) = true := by
  native_decide

theorem h_sep : ∀ x ∈ Xset, ¬ ((∃ r ∈ portsSet, conflict G5 x (bep false r)) ∧
    (∃ r ∈ portsSet, conflict G5 x (bep true r))) := by
  intro x hx hcon
  obtain ⟨h0, h1⟩ := hcon
  rw [fpB_iff] at h0 h1
  have h := List.all_eq_true.mp sepCheck x ((mem_Xset x).mp hx)
  rw [h0, h1] at h
  simp at h

/-- **The pairs are edges**: each parent conflicts with its own alternative.  This is the
`Prop` form of the data-layer `Bool` check `pairConflict`.  With `h_private` it makes
`N[alt r] ∩ I = {r}` an equality. -/
theorem h_ep_conflict : ∀ r ∈ portsSet, conflict G5 r (bep (!bside r) r) := by
  intro r hr
  have hb : wconf (bep (bside r) r) (bep (!bside r) r) = true := by
    simpa using List.all_eq_true.mp pairConflict r ((mem_portsSet r).mp hr)
  rw [h_ep_parent r hr] at hb
  exact (conflict_G5 _ _).mpr hb

/-! ### The assembled system -/

/-- **The Polak--Schrijver base system.** -/
def base : RichPortSystem G5 where
  I := Iset
  hI := isIndepSet_of_pairwiseOK pairwiseOK_I
  ports := portsSet
  hports := h_ports
  ep := bep
  side := bside
  hep_parent := h_ep_parent
  halt_not := h_alt_not
  hprivate := h_private
  hep_conflict := h_ep_conflict
  halt_inj := h_alt_inj
  hP_indep := h_P_indep
  X := Xset
  hX := isIndepSet_of_pairwiseOK pairwiseOK_X
  hsep := h_sep

/-! ### Derived parameters, certified on raw lists -/

theorem IlenCheck : Ilist.length = 367 := by native_decide
theorem portsLenCheck : portsList.length = 8 := by native_decide
theorem XlenCheck : Xlist.length = 367 := by native_decide

theorem base_N : base.N = 367 := by
  change Ilist.length = 367
  exact IlenCheck

theorem base_d : base.d = 8 := by
  change portsList.length = 8
  exact portsLenCheck

theorem base_L : base.L = 367 := by
  change Xlist.length = 367
  exact XlenCheck

/-- `Xlist` has no duplicates, inherited from the data-layer `Finset`. -/
lemma Xlist_nodup : Xlist.Nodup := by
  exact Multiset.coe_nodup.mp
    (show (Xlist : Multiset Code).Nodup from Xset.nodup)

/-- A footprint Finset whose value is literally a filtered list. -/
def Xc (c : Bool) : Finset Code :=
  ⟨(Xlist.filter (fpB c) : Multiset Code),
    Multiset.coe_nodup.mpr (List.Nodup.filter (fpB c) Xlist_nodup)⟩

/-- Membership in `Xc` never mentions a `Finset` bounded existential. -/
lemma mem_Xc {c : Bool} {x : Code} :
    x ∈ Xc c ↔ x ∈ Xlist ∧ fpB c x = true := by
  rw [Xc, Finset.mem_mk, Multiset.mem_coe, List.mem_filter]

/-- Symbolically identify the structure footprint with the literal-list one. -/
lemma Xc_eq (c : Bool) : base.Xc c = Xc c := by
  ext x
  rw [RichPortSystem.mem_Xc, mem_Xc]
  change
    (x ∈ Xset ∧ ∃ r ∈ portsSet, conflict G5 x (bep c r)) ↔
      x ∈ Xlist ∧ fpB c x = true
  rw [mem_Xset, fpB_iff]

theorem XcFalseLenCheck : (Xlist.filter (fpB false)).length = 19 := by
  native_decide

theorem XcTrueLenCheck : (Xlist.filter (fpB true)).length = 26 := by
  native_decide

theorem base_Xc_false : (base.Xc false).card = 19 := by
  rw [Xc_eq]
  change (Xlist.filter (fpB false)).length = 19
  exact XcFalseLenCheck

theorem base_Xc_true : (base.Xc true).card = 26 := by
  rw [Xc_eq]
  change (Xlist.filter (fpB true)).length = 26
  exact XcTrueLenCheck

/-- Compute `eta` from the three certified cardinalities and symbolic disjointness. -/
theorem base_eta : base.eta = 322 := by
  change (Xset \ (base.Xc false ∪ base.Xc true)).card = 322
  have hsub : base.Xc false ∪ base.Xc true ⊆ Xset := by
    change base.Xc false ∪ base.Xc true ⊆ base.X
    exact Finset.union_subset (base.Xc_subset_X false) (base.Xc_subset_X true)
  rw [Finset.card_sdiff_of_subset hsub]
  rw [Finset.card_union_of_disjoint base.Xc_disjoint]
  rw [base_Xc_false, base_Xc_true]
  have hXcard : Xset.card = 367 := by
    change Xlist.length = 367
    exact XlenCheck
  rw [hXcard]

end BaseC7
end ShannonBounds
