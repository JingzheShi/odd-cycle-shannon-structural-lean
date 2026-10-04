/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.Layered

/-!
# The seven families of a port system

A `RichPortSystem` carries an independent set `I` with `d` private pairs and an auxiliary
independent set `X`.  Splitting those into seven pieces

* `B`, the core `I` without the parents;
* `N`, the neutral part of `X`;
* `A` and `D`, the two footprints of `X`;
* `O`, the parents;
* `H` and `V`, the two transversals;

gives a realisation of a fixed seven-letter separation system.  This file proves that every
`RichPortSystem` is such a realisation, and computes the seven family sizes in terms of the
aggregates `(N, d, L, η)` used by `Lift.lean`.
-/

namespace ShannonBounds

open SimpleGraph

/-- The seven letters. -/
inductive Letter | B | N | A | D | O | H | V
  deriving DecidableEq, Fintype, Repr

namespace Letter

/-- The separation table.  It is symmetric and irreflexive, which `sep_symm` and
`sep_irrefl` below record. -/
def sep : Letter → Letter → Bool
  | B, O => true | B, H => true | B, V => true
  | N, A => true | N, D => true | N, O => true | N, H => true | N, V => true
  | A, N => true | A, D => true | A, H => true
  | D, N => true | D, A => true | D, V => true
  | O, B => true | O, N => true
  | H, B => true | H, N => true | H, A => true
  | V, B => true | V, N => true | V, D => true
  | _, _ => false

lemma sep_symm (a b : Letter) : sep a b = sep b a := by cases a <;> cases b <;> rfl

lemma sep_irrefl (a : Letter) : sep a a = false := by cases a <;> rfl

end Letter

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

namespace RichPortSystem

variable (S : RichPortSystem G)

/-- The seven families. -/
def fam : Letter → Finset α
  | .B => S.I \ S.ports
  | .N => S.Xstar
  | .A => S.Xc false
  | .D => S.Xc true
  | .O => S.ports
  | .H => S.ports.image (S.ep true)
  | .V => S.ports.image (S.ep false)

/-! ### Independence of each family -/

/-- A transversal is independent: that is exactly `hP_indep`. -/
lemma isIndepSet_image_ep (c : Bool) : G.IsIndepSet ↑(S.ports.image (S.ep c)) := by
  intro x hx y hy hne hadj
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨s, hs, rfl⟩ := hy
  exact S.hP_indep c r hr s hs (fun h => hne (by rw [h])) (Or.inr hadj)

lemma isIndepSet_fam (a : Letter) : G.IsIndepSet ↑(S.fam a) := by
  have hsub : ∀ {s t : Finset α}, s ⊆ t → G.IsIndepSet ↑t → G.IsIndepSet ↑s :=
    fun h ht => ht.mono (by exact_mod_cast h)
  cases a
  · exact hsub Finset.sdiff_subset S.hI
  · exact hsub S.Xstar_subset_X S.hX
  · exact hsub (S.Xc_subset_X false) S.hX
  · exact hsub (S.Xc_subset_X true) S.hX
  · exact hsub S.hports S.hI
  · exact S.isIndepSet_image_ep true
  · exact S.isIndepSet_image_ep false

/-! ### The eleven separations

Each is a one-line consequence of a lemma already in `Lift.lean`. -/

lemma sep_symm_of {P Q : Finset α} (h : Sep G P Q) : Sep G Q P :=
  fun x hx y hy hc => h y hy x hx (conflict_symm hc)

/-- The core does not meet the parents, and both lie in the independent set `I`. -/
lemma sep_core_ports : Sep G (S.I \ S.ports) S.ports := by
  intro x hx y hy
  rw [Finset.mem_sdiff] at hx
  exact not_conflict_of_indep S.hI hx.1 (S.hports hy)
    (fun he => hx.2 (by rw [he]; exact hy))

/-- The core does not meet either transversal: `not_conflict_core_ep`. -/
lemma sep_core_transversal (c : Bool) :
    Sep G (S.I \ S.ports) (S.ports.image (S.ep c)) := by
  intro x hx y hy
  rw [Finset.mem_sdiff] at hx
  rw [Finset.mem_image] at hy
  obtain ⟨r, hr, rfl⟩ := hy
  exact S.not_conflict_core_ep hx.1 hx.2 c hr

/-- A neutral word meets neither footprint, and both lie in the independent set `X`. -/
lemma sep_neutral_footprint (c : Bool) : Sep G S.Xstar (S.Xc c) := by
  intro x hx y hy
  refine not_conflict_of_indep S.hX (S.Xstar_subset_X hx) (S.Xc_subset_X c hy) ?_
  rintro rfl
  obtain ⟨-, h0, h1⟩ := S.mem_Xstar.mp hx
  cases c
  · exact h0 hy
  · exact h1 hy

/-- A neutral word avoids every endpoint: `not_conflict_epO_of_mem_Xstar`. -/
lemma sep_neutral_ports : Sep G S.Xstar S.ports := by
  intro x hx y hy
  exact S.not_conflict_epO_of_mem_Xstar hx none hy

lemma sep_neutral_transversal (c : Bool) :
    Sep G S.Xstar (S.ports.image (S.ep c)) := by
  intro x hx y hy
  rw [Finset.mem_image] at hy
  obtain ⟨r, hr, rfl⟩ := hy
  exact S.not_conflict_ep_of_mem_Xstar hx c hr

/-- The two footprints are disjoint, which is `hsep`, and both lie in `X`. -/
lemma sep_footprints : Sep G (S.Xc false) (S.Xc true) := by
  intro x hx y hy
  refine not_conflict_of_indep S.hX (S.Xc_subset_X false hx) (S.Xc_subset_X true hy) ?_
  rintro rfl
  exact S.notMem_Xc_of_mem_Xc hx hy

/-- A word in one footprint cannot touch the *other* transversal: it would then lie in
both footprints, which `hsep` forbids. -/
lemma sep_footprint_other_transversal (c : Bool) :
    Sep G (S.Xc c) (S.ports.image (S.ep (!c))) := by
  intro x hx y hy hcf
  rw [Finset.mem_image] at hy
  obtain ⟨r, hr, rfl⟩ := hy
  exact S.notMem_Xc_of_mem_Xc hx (S.mem_Xc_of_conflict (S.Xc_subset_X c hx) hr hcf)

lemma sep_fam (a b : Letter) (hab : Letter.sep a b = true) : Sep G (S.fam a) (S.fam b) := by
  cases a <;> cases b <;> simp only [Letter.sep, reduceCtorEq] at hab ⊢
  · exact S.sep_core_ports
  · exact S.sep_core_transversal true
  · exact S.sep_core_transversal false
  · exact S.sep_neutral_footprint false
  · exact S.sep_neutral_footprint true
  · exact S.sep_neutral_ports
  · exact S.sep_neutral_transversal true
  · exact S.sep_neutral_transversal false
  · exact sep_symm_of (S.sep_neutral_footprint false)
  · exact S.sep_footprints
  · exact S.sep_footprint_other_transversal false
  · exact sep_symm_of (S.sep_neutral_footprint true)
  · exact sep_symm_of S.sep_footprints
  · exact S.sep_footprint_other_transversal true
  · exact sep_symm_of S.sep_core_ports
  · exact sep_symm_of S.sep_neutral_ports
  · exact sep_symm_of (S.sep_core_transversal true)
  · exact sep_symm_of (S.sep_neutral_transversal true)
  · exact sep_symm_of (S.sep_footprint_other_transversal false)
  · exact sep_symm_of (S.sep_core_transversal false)
  · exact sep_symm_of (S.sep_neutral_transversal false)
  · exact sep_symm_of (S.sep_footprint_other_transversal true)

/-- **Every port system is a realisation of the seven-letter separation system.** -/
def toRealisation : Realisation Letter Letter.sep G where
  P := S.fam
  hindep := S.isIndepSet_fam
  hsep := S.sep_fam

/-! ### The seven sizes -/

/-- `ep c` is injective on the parents: two equal endpoints would conflict. -/
lemma ep_injOn (c : Bool) : Set.InjOn (S.ep c) ↑S.ports := by
  intro r hr s hs he
  by_contra hne
  exact S.hP_indep c r hr s hs hne (Or.inl he)

@[simp] lemma card_fam_O : (S.fam .O).card = S.d := rfl

@[simp] lemma card_fam_H : (S.fam .H).card = S.d :=
  Finset.card_image_of_injOn (S.ep_injOn true)

@[simp] lemma card_fam_V : (S.fam .V).card = S.d :=
  Finset.card_image_of_injOn (S.ep_injOn false)

@[simp] lemma card_fam_B : (S.fam .B).card = S.N - S.d := by
  show (S.I \ S.ports).card = S.I.card - S.ports.card
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr S.hports]

@[simp] lemma card_fam_N : (S.fam .N).card = S.eta := rfl

/-- The weights of the realisation, letter by letter. -/
lemma w_toRealisation (a : Letter) : S.toRealisation.w a = (S.fam a).card := rfl

end RichPortSystem

end ShannonBounds
