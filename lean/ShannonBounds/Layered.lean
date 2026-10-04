/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.Lift
import ShannonBounds.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Layered substitutions

A finite separation system is an alphabet with a symmetric irreflexive relation `sep`.  It is
realised in a graph by a family of independent sets, one per letter, with `P a` separated from
`P b` whenever `sep a b`.  An admissible substitution replaces each letter by a set of words,
in a way that preserves both properties, and so carries one realisation to another in a higher
power.  Iterating gives an independent set whose size is the corresponding composition of
polynomial maps.

`liftRPS` in `Lift.lean` is the arity-2 case with a fixed substitution; here the arity and the
substitution may differ at each layer.
-/

namespace ShannonBounds

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two sets are separated when no vertex of one conflicts with a vertex of the other. -/
def Sep (G : SimpleGraph V) [DecidableRel G.Adj] (P Q : Finset V) : Prop :=
  ∀ x ∈ P, ∀ y ∈ Q, ¬ conflict G x y

/-- A realisation of a separation system `sep` on the alphabet `A` by sets in `G`. -/
structure Realisation (A : Type*) [Fintype A] (sep : A → A → Bool)
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- the set attached to each letter -/
  P : A → Finset V
  hindep : ∀ a, G.IsIndepSet ↑(P a)
  hsep : ∀ a b, sep a b = true → Sep G (P a) (P b)

/-- The weight of a letter is the size of its set. -/
def Realisation.w {A : Type*} [Fintype A] {sep : A → A → Bool}
    {G : SimpleGraph V} [DecidableRel G.Adj] (R : Realisation A sep G) (a : A) : ℕ :=
  (R.P a).card


/-- The set of tuples realising a word: coordinate `i` ranges over the set of letter `x i`. -/
def wordSet {A : Type*} [Fintype A] {sep : A → A → Bool}
    {G : SimpleGraph V} [DecidableRel G.Adj] (R : Realisation A sep G) {q : ℕ}
    (x : Fin q → A) : Finset (Fin q → V) :=
  Fintype.piFinset (fun i => R.P (x i))

variable {A : Type*} [Fintype A] [DecidableEq A] {sep : A → A → Bool}
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq A] in
lemma card_wordSet (R : Realisation A sep G) {q : ℕ} (x : Fin q → A) :
    (wordSet R x).card = ∏ i, R.w (x i) := by
  simp [wordSet, Fintype.card_piFinset, Realisation.w]

omit [DecidableEq A] in
/-- Each word set is independent in the strong power. -/
lemma isIndepSet_wordSet (R : Realisation A sep G) {q : ℕ} (x : Fin q → A) :
    (SimpleGraph.strongPower G q).IsIndepSet ↑(wordSet R x) := by
  intro f hf g hg hne hadj
  obtain ⟨-, h⟩ := hadj
  simp only [Finset.mem_coe, wordSet, Fintype.mem_piFinset] at hf hg
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  rcases h i with he | hA
  · exact hi he
  · exact R.hindep (x i) (hf i) (hg i) hi hA

omit [DecidableEq A] in
/-- Words separated in one coordinate give separated sets. -/
lemma sep_wordSet (R : Realisation A sep G) {q : ℕ} {x y : Fin q → A}
    (h : ∃ i, sep (x i) (y i) = true) :
    Sep (SimpleGraph.strongPower G q) (wordSet R x) (wordSet R y) := by
  obtain ⟨i, hi⟩ := h
  intro f hf g hg hc
  simp only [wordSet, Fintype.mem_piFinset] at hf hg
  rcases hc with rfl | ⟨-, hall⟩
  · exact R.hsep _ _ hi (f i) (hf i) (f i) (hg i) (Or.inl rfl)
  · rcases hall i with he | hA
    · exact R.hsep _ _ hi (f i) (hf i) (g i) (hg i) (Or.inl he)
    · exact R.hsep _ _ hi (f i) (hf i) (g i) (hg i) (Or.inr hA)

/-- An admissible substitution of arity `q`. -/
structure Subst (A : Type*) [Fintype A] (sep : A → A → Bool) (q : ℕ) where
  /-- the words replacing each letter -/
  T : A → Finset (Fin q → A)
  /-- distinct words of one letter are separated in a coordinate -/
  hin : ∀ a, ∀ x ∈ T a, ∀ y ∈ T a, x ≠ y → ∃ i, sep (x i) (y i) = true
  /-- words of separated letters are separated in a coordinate -/
  hcross : ∀ a b, sep a b = true → ∀ x ∈ T a, ∀ y ∈ T b, ∃ i, sep (x i) (y i) = true


/-- The set attached to a letter after substitution: the union over its words. -/
def substSet (R : Realisation A sep G) {q : ℕ} (S : Subst A sep q) (a : A) :
    Finset (Fin q → V) := (S.T a).biUnion (wordSet R)

/-- Distinct words of one letter give disjoint sets, so the union counts exactly. -/
lemma card_substSet (R : Realisation A sep G) {q : ℕ} (S : Subst A sep q) (a : A) :
    (substSet R S a).card = ∑ x ∈ S.T a, ∏ i, R.w (x i) := by
  have hd : ∀ x ∈ S.T a, ∀ y ∈ S.T a, x ≠ y → Disjoint (wordSet R x) (wordSet R y) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro f hf hf'
    exact sep_wordSet R (S.hin a x hx y hy hne) f hf f hf' (Or.inl rfl)
  rw [substSet, Finset.card_biUnion hd]
  exact Finset.sum_congr rfl fun x _ => card_wordSet R x

/-- **The substitution step.**  An admissible substitution carries a realisation in `G` to a
realisation in `G^⊠q`, with the weights transformed by the polynomial map. -/
def Realisation.subst (R : Realisation A sep G) {q : ℕ} (S : Subst A sep q) :
    Realisation A sep (SimpleGraph.strongPower G q) where
  P := substSet R S
  hindep := by
    intro a f hf g hg hne hadj
    simp only [Finset.mem_coe, substSet, Finset.mem_biUnion] at hf hg
    obtain ⟨x, hx, hfx⟩ := hf
    obtain ⟨y, hy, hgy⟩ := hg
    by_cases hxy : x = y
    · subst hxy
      exact isIndepSet_wordSet R x hfx hgy hne hadj
    · exact sep_wordSet R (S.hin a x hx y hy hxy) f hfx g hgy (Or.inr hadj)
  hsep := by
    intro a b hab f hf g hg hc
    simp only [substSet, Finset.mem_biUnion] at hf hg
    obtain ⟨x, hx, hfx⟩ := hf
    obtain ⟨y, hy, hgy⟩ := hg
    exact sep_wordSet R (S.hcross a b hab x hx y hy) f hfx g hgy hc

@[simp] lemma w_subst (R : Realisation A sep G) {q : ℕ} (S : Subst A sep q) (a : A) :
    (R.subst S).w a = ∑ x ∈ S.T a, ∏ i, R.w (x i) :=
  card_substSet R S a


/-! ### Multilinear substitutions

The ordinary substitution above uses one realisation in every coordinate.  Here the `i`-th
coordinate may instead use a realisation in `G^(⊠ e i)`.  Their vertex sets form a dependent
product, which is reindexed to `Fin (∑ i, e i) → V` below.
-/

/-- The componentwise strong product of the powers `G^(⊠ e i)`. -/
def familyStrongPower (G : SimpleGraph V) {q : ℕ} (e : Fin q → ℕ) :
    SimpleGraph ((i : Fin q) → Fin (e i) → V) where
  Adj f g := f ≠ g ∧ ∀ i, f i = g i ∨ (SimpleGraph.strongPower G (e i)).Adj (f i) (g i)
  symm := ⟨by
    intro f g ⟨hne, h⟩
    refine ⟨hne.symm, fun i => ?_⟩
    rcases h i with he | ha
    · exact Or.inl he.symm
    · exact Or.inr ha.symm⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Adjacency in a componentwise family of strong powers is decidable. -/
instance familyStrongPower_adj_decidable (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (e : Fin q → ℕ) : DecidableRel (familyStrongPower G e).Adj :=
  fun f g => by
    change Decidable (f ≠ g ∧ ∀ i, f i = g i ∨ (SimpleGraph.strongPower G (e i)).Adj (f i) (g i))
    exact instDecidableAnd

/-- Reindex one tuple of summed length as a dependent tuple of blocks. -/
def sumEquiv {q : ℕ} (e : Fin q → ℕ) (V : Type*) :
    (Fin (∑ i, e i) → V) ≃ ((i : Fin q) → Fin (e i) → V) :=
  (Equiv.piCongrLeft' (fun _ : Fin (∑ i, e i) => V) finSigmaFinEquiv.symm).trans
    (Equiv.piCurry fun _ _ => V)

/-- The same reindexing in the flattening direction. -/
def flattenSumEquiv {q : ℕ} (e : Fin q → ℕ) (V : Type*) :
    ((i : Fin q) → Fin (e i) → V) ≃ (Fin (∑ i, e i) → V) :=
  (sumEquiv e V).symm

omit [Fintype V] [DecidableEq V] in
@[simp] lemma sumEquiv_apply {q : ℕ} (e : Fin q → ℕ)
    (f : Fin (∑ i, e i) → V) (i : Fin q) (j : Fin (e i)) :
    sumEquiv e V f i j = f (finSigmaFinEquiv ⟨i, j⟩) := by
  rfl

/-- **Summed powers are componentwise powers.**  This is the heterogeneous analogue of
`strongPower_mul_iso`. -/
def strongPower_sum_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (e : Fin q → ℕ) :
    SimpleGraph.strongPower G (∑ i, e i) ≃g familyStrongPower G e where
  toEquiv := sumEquiv e V
  map_rel_iff' := by
    intro f g
    show (_ ≠ _ ∧ ∀ i, _ = _ ∨ _) ↔ (f ≠ g ∧ ∀ k, _)
    constructor
    · rintro ⟨hne, h⟩
      refine ⟨fun hfg => hne (by rw [hfg]), fun k => ?_⟩
      let p := finSigmaFinEquiv.symm k
      have hk : finSigmaFinEquiv p = k := finSigmaFinEquiv.apply_symm_apply k
      rcases p with ⟨i, j⟩
      subst k
      rcases h i with he | ha
      · left
        exact congrFun he j
      · exact ha.2 j
    · rintro ⟨hne, h⟩
      refine ⟨fun he => hne ((sumEquiv e V).injective he), fun i => ?_⟩
      by_cases he : sumEquiv e V f i = sumEquiv e V g i
      · exact Or.inl he
      · refine Or.inr ⟨he, fun j => ?_⟩
        simpa only [sumEquiv_apply] using h (finSigmaFinEquiv ⟨i, j⟩)

/-- Transport a realisation forward along a graph isomorphism. -/
def Realisation.mapIso {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (R : Realisation A sep G) (f : G ≃g H) :
    Realisation A sep H where
  P a := (R.P a).image f
  hindep := by
    intro a x hx y hy hne ha
    simp only [Finset.mem_coe, Finset.mem_image] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact R.hindep a hx' hy' (fun he => hne (congrArg f he)) (f.map_rel_iff.mp ha)
  hsep := by
    intro a b hab x hx y hy hc
    simp only [Finset.mem_image] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    apply R.hsep a b hab x' hx' y' hy'
    rcases hc with he | ha
    · exact Or.inl (f.injective he)
    · exact Or.inr (f.map_rel_iff.mp ha)

@[simp] lemma Realisation.w_mapIso {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (R : Realisation A sep G) (f : G ≃g H) (a : A) :
    (R.mapIso f).w a = R.w a := by
  simp [Realisation.mapIso, Realisation.w, Finset.card_image_of_injective _ f.injective]

/-- A graph is canonically its first strong power. -/
def strongPower_one_iso (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph.strongPower G 1 ≃g G where
  toEquiv :=
    { toFun := fun f => f 0
      invFun := fun x _ => x
      left_inv := by intro f; funext i; rw [Fin.eq_zero i]
      right_inv := by intro x; rfl }
  map_rel_iff' := by
    intro f g
    constructor
    · intro ha
      refine ⟨fun he => ?_, fun i => Or.inr (by simpa [Fin.eq_zero i] using ha)⟩
      exact ha.ne (congrFun he 0)
    · rintro ⟨hne, h⟩
      rcases h 0 with he | ha
      · exact (hne (by funext i; simpa [Fin.eq_zero i] using he)).elim
      · exact ha

/-- The tuples realising a word when coordinate `i` has its own realisation. -/
def multiWordSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (x : Fin q → A) : Finset ((i : Fin q) → Fin (e i) → V) :=
  Fintype.piFinset (fun i => (R i).P (x i))

omit [DecidableEq A] in
lemma card_multiWordSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (x : Fin q → A) :
    (multiWordSet e R x).card = ∏ i, (R i).w (x i) := by
  simp [multiWordSet, Fintype.card_piFinset, Realisation.w]

omit [DecidableEq A] in
lemma isIndepSet_multiWordSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (x : Fin q → A) :
    (familyStrongPower G e).IsIndepSet ↑(multiWordSet e R x) := by
  intro f hf g hg hne hadj
  simp only [Finset.mem_coe, multiWordSet, Fintype.mem_piFinset] at hf hg
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  rcases hadj.2 i with he | ha
  · exact hi he
  · exact (R i).hindep (x i) (hf i) (hg i) hi ha

omit [DecidableEq A] in
lemma sep_multiWordSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    {x y : Fin q → A} (h : ∃ i, sep (x i) (y i) = true) :
    Sep (familyStrongPower G e) (multiWordSet e R x) (multiWordSet e R y) := by
  obtain ⟨i, hi⟩ := h
  intro f hf g hg hc
  simp only [multiWordSet, Fintype.mem_piFinset] at hf hg
  apply (R i).hsep _ _ hi (f i) (hf i) (g i) (hg i)
  rcases hc with he | ha
  · exact Or.inl (congrFun he i)
  · exact ha.2 i

/-- The union of heterogeneous word sets attached to a letter. -/
def multiSubstSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (S : Subst A sep q) (a : A) : Finset ((i : Fin q) → Fin (e i) → V) :=
  (S.T a).biUnion (multiWordSet e R)

lemma card_multiSubstSet {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (S : Subst A sep q) (a : A) :
    (multiSubstSet e R S a).card = ∑ x ∈ S.T a, ∏ i, (R i).w (x i) := by
  have hd : ∀ x ∈ S.T a, ∀ y ∈ S.T a, x ≠ y →
      Disjoint (multiWordSet e R x) (multiWordSet e R y) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro f hf hf'
    exact sep_multiWordSet e R (S.hin a x hx y hy hne) f hf f hf' (Or.inl rfl)
  rw [multiSubstSet, Finset.card_biUnion hd]
  exact Finset.sum_congr rfl fun x _ => card_multiWordSet e R x

/-- The multilinear substitution, before flattening the dependent blocks. -/
def Realisation.multiSubstFamily {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (S : Subst A sep q) : Realisation A sep (familyStrongPower G e) where
  P := multiSubstSet e R S
  hindep := by
    intro a f hf g hg hne hadj
    simp only [Finset.mem_coe, multiSubstSet, Finset.mem_biUnion] at hf hg
    obtain ⟨x, hx, hfx⟩ := hf
    obtain ⟨y, hy, hgy⟩ := hg
    by_cases hxy : x = y
    · subst hxy
      exact isIndepSet_multiWordSet e R x hfx hgy hne hadj
    · exact sep_multiWordSet e R (S.hin a x hx y hy hxy) f hfx g hgy (Or.inr hadj)
  hsep := by
    intro a b hab f hf g hg hc
    simp only [multiSubstSet, Finset.mem_biUnion] at hf hg
    obtain ⟨x, hx, hfx⟩ := hf
    obtain ⟨y, hy, hgy⟩ := hg
    exact sep_multiWordSet e R (S.hcross a b hab x hx y hy) f hfx g hgy hc

/-- **The multilinear substitution step.**  Coordinate `i` uses the realisation `R i`, and
the resulting exponent is the sum of the child exponents. -/
def Realisation.multiSubst {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (S : Subst A sep q) : Realisation A sep (SimpleGraph.strongPower G (∑ i, e i)) :=
  (Realisation.multiSubstFamily e R S).mapIso (strongPower_sum_iso G e).symm

@[simp] lemma w_multiSubst {q : ℕ} (e : Fin q → ℕ)
    (R : (i : Fin q) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (S : Subst A sep q) (a : A) :
    (Realisation.multiSubst e R S).w a = ∑ x ∈ S.T a, ∏ i, (R i).w (x i) := by
  rw [Realisation.multiSubst, Realisation.w_mapIso]
  exact card_multiSubstSet e R S a

/-- Before flattening, multilinear substitution with a constant exponent and one repeated
child realisation is definitionally `Realisation.subst`. -/
lemma multiSubstFamily_const {q k : ℕ}
    (R : Realisation A sep (SimpleGraph.strongPower G k)) (S : Subst A sep q) :
    Realisation.multiSubstFamily (fun _ : Fin q => k) (fun _ => R) S = R.subst S := by
  rfl

/-- After flattening, a constant exponent and one repeated child realisation give
`Realisation.subst` transported along the summed-power isomorphism. -/
lemma multiSubst_const {q k : ℕ}
    (R : Realisation A sep (SimpleGraph.strongPower G k)) (S : Subst A sep q) :
    Realisation.multiSubst (fun _ : Fin q => k) (fun _ => R) S =
      (R.subst S).mapIso (strongPower_sum_iso G (fun _ : Fin q => k)).symm := by
  unfold Realisation.multiSubst
  congr 1

/-- Consequently, a constant exponent and one repeated child realisation give exactly the
weight transformation of `Realisation.subst`. -/
lemma w_multiSubst_const {q k : ℕ}
    (R : Realisation A sep (SimpleGraph.strongPower G k)) (S : Subst A sep q) (a : A) :
    (Realisation.multiSubst (fun _ : Fin q => k) (fun _ => R) S).w a = (R.subst S).w a := by
  rw [w_multiSubst, w_subst]

/-- In particular, under the canonical identification `G ≃ G^(⊠1)`, multilinear substitution
with all exponents `1` has the weight transformation of `Realisation.subst`. -/
lemma w_multiSubst_one {q : ℕ} (R : Realisation A sep G) (S : Subst A sep q) (a : A) :
    (Realisation.multiSubst (fun _ : Fin q => 1)
      (fun _ => R.mapIso (strongPower_one_iso G).symm) S).w a = (R.subst S).w a := by
  rw [w_multiSubst, w_subst]
  simp only [Realisation.w_mapIso]


/-- A terminal code: a set of words that are pairwise separated in some coordinate. -/
structure Code (A : Type*) [Fintype A] (sep : A → A → Bool) (r : ℕ) where
  /-- the words of the code -/
  C : Finset (Fin r → A)
  hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ∃ i, sep (x i) (y i) = true

/-- The independent set a terminal code produces. -/
def codeSet (R : Realisation A sep G) {r : ℕ} (K : Code A sep r) : Finset (Fin r → V) :=
  K.C.biUnion (wordSet R)

/-- **The layered count.**  A terminal code over a realisation gives an independent set
whose size is the sum over its words of the product of the weights. -/
theorem card_codeSet (R : Realisation A sep G) {r : ℕ} (K : Code A sep r) :
    (codeSet R K).card = ∑ x ∈ K.C, ∏ i, R.w (x i) := by
  have hd : ∀ x ∈ K.C, ∀ y ∈ K.C, x ≠ y → Disjoint (wordSet R x) (wordSet R y) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro f hf hf'
    exact sep_wordSet R (K.hsep x hx y hy hne) f hf f hf' (Or.inl rfl)
  rw [codeSet, Finset.card_biUnion hd]
  exact Finset.sum_congr rfl fun x _ => card_wordSet R x

/-- The set a terminal code produces is independent. -/
theorem isIndepSet_codeSet (R : Realisation A sep G) {r : ℕ} (K : Code A sep r) :
    (SimpleGraph.strongPower G r).IsIndepSet ↑(codeSet R K) := by
  intro f hf g hg hne hadj
  simp only [Finset.mem_coe, codeSet, Finset.mem_biUnion] at hf hg
  obtain ⟨x, hx, hfx⟩ := hf
  obtain ⟨y, hy, hgy⟩ := hg
  by_cases hxy : x = y
  · subst hxy; exact isIndepSet_wordSet R x hfx hgy hne hadj
  · exact sep_wordSet R (K.hsep x hx y hy hxy) f hfx g hgy (Or.inr hadj)

/-- **The layered bound.**  Applying a terminal code to a realisation bounds the
independence number of the strong power from below. -/
theorem le_indepNum_codeSet (R : Realisation A sep G) {r : ℕ} (K : Code A sep r) :
    (∑ x ∈ K.C, ∏ i, R.w (x i)) ≤ (SimpleGraph.strongPower G r).indepNum :=
  le_trans (le_of_eq (card_codeSet R K).symm)
    (SimpleGraph.IsIndepSet.card_le_indepNum (isIndepSet_codeSet R K))

/-- The independent set produced by a code whose coordinates use different realisations. -/
def multiCodeSet {r : ℕ} (e : Fin r → ℕ)
    (R : (i : Fin r) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (K : Code A sep r) : Finset ((i : Fin r) → Fin (e i) → V) :=
  K.C.biUnion (multiWordSet e R)

/-- The heterogeneous terminal count. -/
lemma card_multiCodeSet {r : ℕ} (e : Fin r → ℕ)
    (R : (i : Fin r) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (K : Code A sep r) :
    (multiCodeSet e R K).card = ∑ x ∈ K.C, ∏ i, (R i).w (x i) := by
  have hd : ∀ x ∈ K.C, ∀ y ∈ K.C, x ≠ y →
      Disjoint (multiWordSet e R x) (multiWordSet e R y) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro f hf hf'
    exact sep_multiWordSet e R (K.hsep x hx y hy hne) f hf f hf' (Or.inl rfl)
  rw [multiCodeSet, Finset.card_biUnion hd]
  exact Finset.sum_congr rfl fun x _ => card_multiWordSet e R x

/-- The heterogeneous terminal set is independent in the componentwise product. -/
lemma isIndepSet_multiCodeSet {r : ℕ} (e : Fin r → ℕ)
    (R : (i : Fin r) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (K : Code A sep r) :
    (familyStrongPower G e).IsIndepSet ↑(multiCodeSet e R K) := by
  intro f hf g hg hne hadj
  simp only [Finset.mem_coe, multiCodeSet, Finset.mem_biUnion] at hf hg
  obtain ⟨x, hx, hfx⟩ := hf
  obtain ⟨y, hy, hgy⟩ := hg
  by_cases hxy : x = y
  · subst hxy
    exact isIndepSet_multiWordSet e R x hfx hgy hne hadj
  · exact sep_multiWordSet e R (K.hsep x hx y hy hxy) f hfx g hgy (Or.inr hadj)


/-! ### Flattening a power of a power

Two substitution layers land in `strongPower (strongPower G q) r`.  Reindexing along
`Fin q × Fin r ≃ Fin (q * r)` identifies that with `strongPower G (q * r)`, so layers
compose and the final bound is about a single strong power of `G`. -/

/-- The reindexing `(Fin (q*r) → V) ≃ (Fin r → Fin q → V)`. -/
def flatEquiv (q r : ℕ) (V : Type*) : (Fin (q * r) → V) ≃ (Fin r → Fin q → V) where
  toFun f i j := f (finProdFinEquiv (j, i))
  invFun g k := g (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  left_inv f := by
    funext k
    show f (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = f k
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv g := by
    funext i j
    show g (finProdFinEquiv.symm (finProdFinEquiv (j, i))).2
           (finProdFinEquiv.symm (finProdFinEquiv (j, i))).1 = g i j
    rw [Equiv.symm_apply_apply]

omit [Fintype V] [DecidableEq V] in
lemma flatEquiv_apply (q r : ℕ) (f : Fin (q * r) → V) (i : Fin r) (j : Fin q) :
    flatEquiv q r V f i j = f (finProdFinEquiv (j, i)) := rfl

omit [Fintype V] [DecidableEq V] in
/-- Not-everywhere-equal transports across the reindexing. -/
lemma flatEquiv_ne_iff (q r : ℕ) (f g : Fin (q * r) → V) :
    flatEquiv q r V f ≠ flatEquiv q r V g ↔ f ≠ g := by
  constructor
  · intro h he; exact h (by rw [he])
  · intro h he; exact h ((flatEquiv q r V).injective he)

/-- **Flattening.**  `strongPower G (q*r) ≃g strongPower (strongPower G q) r`. -/
def strongPower_mul_iso (G : SimpleGraph V) [DecidableRel G.Adj] (q r : ℕ) :
    SimpleGraph.strongPower G (q * r) ≃g
      SimpleGraph.strongPower (SimpleGraph.strongPower G q) r where
  toEquiv := flatEquiv q r V
  map_rel_iff' := by
    intro f g
    show (_ ≠ _ ∧ _) ↔ (_ ≠ _ ∧ _)
    rw [flatEquiv_ne_iff]
    refine and_congr_right fun _ => ⟨fun h k => ?_, fun h i => ?_⟩
    · have hk := h (finProdFinEquiv.symm k).2
      rcases hk with he | ⟨-, hall⟩
      · left
        have := congrFun he (finProdFinEquiv.symm k).1
        rw [flatEquiv_apply, flatEquiv_apply, Prod.mk.eta, Equiv.apply_symm_apply] at this
        exact this
      · rcases hall (finProdFinEquiv.symm k).1 with hh | hh
        · left
          rw [flatEquiv_apply, flatEquiv_apply, Prod.mk.eta, Equiv.apply_symm_apply] at hh
          exact hh
        · right
          rw [flatEquiv_apply, flatEquiv_apply, Prod.mk.eta, Equiv.apply_symm_apply] at hh
          exact hh
    · by_cases he : flatEquiv q r V f i = flatEquiv q r V g i
      · exact Or.inl he
      · refine Or.inr ⟨he, fun j => ?_⟩
        rw [flatEquiv_apply, flatEquiv_apply]
        exact h (finProdFinEquiv (j, i))

/-! ### Transporting a bound along the flattening

`le_indepNum_codeSet` lands in a power of a power.  These two lemmas move a bound down to a
single power of `G`, so that layers of different arity compose into one exponent. -/

/-- An isomorphism carries independent sets backwards. -/
lemma isIndepSet_image_symm {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (e : G ≃g H) {s : Finset W} (hs : H.IsIndepSet ↑s) :
    G.IsIndepSet ↑(s.image e.symm) := by
  intro f hf g hg hne hadj
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hf hg
  obtain ⟨f', hf', rfl⟩ := hf
  obtain ⟨g', hg', rfl⟩ := hg
  refine hs hf' hg' (fun h => hne (by rw [h])) ?_
  simpa using e.map_rel_iff.2 hadj

/-- A lower bound on the independence number transfers backwards along an isomorphism. -/
lemma le_indepNum_of_iso {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (e : G ≃g H) {n : ℕ} {s : Finset W}
    (hs : H.IsIndepSet ↑s) (hn : n ≤ s.card) : n ≤ G.indepNum :=
  le_trans (le_trans hn (le_of_eq (Finset.card_image_of_injective _ e.symm.injective).symm))
    (SimpleGraph.IsIndepSet.card_le_indepNum (isIndepSet_image_symm e hs))

/-- **The heterogeneous terminal step.**  Coordinate `i` of a code uses `R i`, so the
resulting strong-power exponent is the sum of the coordinate exponents. -/
theorem le_indepNum_multiCode {r : ℕ} (e : Fin r → ℕ)
    (R : (i : Fin r) → Realisation A sep (SimpleGraph.strongPower G (e i)))
    (K : Code A sep r) :
    (∑ x ∈ K.C, ∏ i, (R i).w (x i)) ≤
      (SimpleGraph.strongPower G (∑ i, e i)).indepNum :=
  le_indepNum_of_iso (strongPower_sum_iso G e)
    (isIndepSet_multiCodeSet e R K) (le_of_eq (card_multiCodeSet e R K).symm)

/-- **Layer composition.**  A substitution of arity `q` followed by a terminal code of arity `r`
gives a bound on `G^⊠(q*r)`, not on a power of a power. -/
theorem le_indepNum_subst (R : Realisation A sep G) {q r : ℕ}
    (S : Subst A sep q) (K : Code A sep r) :
    (∑ x ∈ K.C, ∏ i, (R.subst S).w (x i)) ≤ (SimpleGraph.strongPower G (q * r)).indepNum :=
  le_indepNum_of_iso (strongPower_mul_iso G q r)
    (isIndepSet_codeSet (R.subst S) K) (le_of_eq (card_codeSet (R.subst S) K).symm)

/-- **Flattening a bound.**  What holds for a power of a power holds for the single power. -/
theorem le_indepNum_flat {n q r : ℕ}
    (h : n ≤ (SimpleGraph.strongPower (SimpleGraph.strongPower G q) r).indepNum) :
    n ≤ (SimpleGraph.strongPower G (q * r)).indepNum := by
  obtain ⟨s, hs, hcard⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := SimpleGraph.strongPower (SimpleGraph.strongPower G q) r)
  exact le_indepNum_of_iso (strongPower_mul_iso G q r) hs (h.trans hcard.ge)

/-- An isomorphism of graphs induces one of their strong powers. -/
def strongPower_congr {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (e : G ≃g H) (k : ℕ) :
    SimpleGraph.strongPower G k ≃g SimpleGraph.strongPower H k where
  toEquiv := Equiv.piCongrRight fun _ => e.toEquiv
  map_rel_iff' := by
    intro x y
    show (_ ≠ _ ∧ _) ↔ (_ ≠ _ ∧ _)
    constructor
    · rintro ⟨hne, h⟩
      refine ⟨fun he => hne (by rw [he]), fun i => ?_⟩
      rcases h i with he | ha
      · exact Or.inl (e.toEquiv.injective he)
      · exact Or.inr (e.map_rel_iff.mp ha)
    · rintro ⟨hne, h⟩
      refine ⟨fun he => hne (funext fun i => e.toEquiv.injective (congrFun he i)), fun i => ?_⟩
      rcases h i with he | ha
      · exact Or.inl (by simp [he])
      · exact Or.inr (e.map_rel_iff.mpr ha)

end ShannonBounds
