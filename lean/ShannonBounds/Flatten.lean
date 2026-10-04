/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# Splitting a strong power

The lift produces nested strong *products*; the Shannon-capacity machinery wants a
strong *power* `strongPower G n` on `Fin n → V`.  The bridge is the reindexing

  `strongPower G (m + n) ≃g strongPower G m ⊠ strongPower G n`

which is `strongPower_add_iso` below.  On vertices it is
`(Fin (m+n) → V) ≃ (Fin m → V) × (Fin n → V)`, restriction along
`Fin.castAdd`/`Fin.natAdd`; on edges both sides say "conflict in every coordinate,
and not everywhere equal", so the transport is a `Fin.addCases` split.

`strongProd_congr` is the matching congruence for the strong product: isomorphic factors
give isomorphic strong products.
-/
import ShannonBounds.Lift
import ShannonBounds.Defs

namespace ShannonBounds

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Conflict in a strong power is coordinatewise conflict -/

omit [Fintype V] in
lemma conflict_strongPower {n : ℕ} [DecidableRel (strongPower G n).Adj]
    (a b : Fin n → V) :
    conflict (strongPower G n) a b ↔ ∀ i, conflict G (a i) (b i) := by
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · exact fun i => conflict_rfl _
    · exact fun i => h i
  · intro h
    by_cases hab : a = b
    · exact Or.inl hab
    · exact Or.inr ⟨hab, fun i => h i⟩

/-! ### Splitting the index set -/

/-- A property holds at every index of `Fin (m + n)` iff it holds on both blocks. -/
lemma forall_fin_add_iff {m n : ℕ} (P : Fin (m + n) → Prop) :
    (∀ k, P k) ↔ (∀ i : Fin m, P (Fin.castAdd n i)) ∧ (∀ j : Fin n, P (Fin.natAdd m j)) := by
  constructor
  · intro h
    exact ⟨fun i => h _, fun j => h _⟩
  · intro ⟨h1, h2⟩ k
    induction k using Fin.addCases with
    | left i => exact h1 i
    | right j => exact h2 j

/-- The reindexing equivalence `(Fin (m+n) → V) ≃ (Fin m → V) × (Fin n → V)`. -/
def splitEquiv (m n : ℕ) (V : Type*) : (Fin (m + n) → V) ≃ (Fin m → V) × (Fin n → V) where
  toFun f := (fun i => f (Fin.castAdd n i), fun j => f (Fin.natAdd m j))
  invFun p := Fin.addCases p.1 p.2
  left_inv f := by
    funext k
    induction k using Fin.addCases with
    | left i => simp
    | right j => simp
  right_inv p := by
    ext i
    · simp
    · simp

/-! ### The splitting isomorphism -/

/-- **`strongPower G (m+n) ≃g strongPower G m ⊠ strongPower G n`.**  Pure reindexing:
both sides say "conflict in every coordinate, and not everywhere equal". -/
def strongPower_add_iso (G : SimpleGraph V) [DecidableRel G.Adj] (m n : ℕ) :
    strongPower G (m + n) ≃g strongProd (strongPower G m) (strongPower G n) where
  toEquiv := splitEquiv m n V
  map_rel_iff' := by
    intro f g
    show (strongProd (strongPower G m) (strongPower G n)).Adj _ _ ↔ _
    rw [strongProd_adj]
    constructor
    · rintro ⟨hne, h1, h2⟩
      refine ⟨fun hfg => hne (by rw [hfg]), ?_⟩
      rw [conflict_strongPower] at h1 h2
      exact (forall_fin_add_iff (fun k => conflict G (f k) (g k))).mpr ⟨h1, h2⟩
    · rintro ⟨hne, h⟩
      have hsplit := (forall_fin_add_iff (fun k => conflict G (f k) (g k))).mp
        (fun k => h k)
      refine ⟨?_, (conflict_strongPower _ _).mpr hsplit.1,
        (conflict_strongPower _ _).mpr hsplit.2⟩
      intro heq
      apply hne
      exact (splitEquiv m n V).injective heq

/-- Congruence for the strong product. -/
def strongProd_congr {V₁ V₂ W₁ W₂ : Type*} [Fintype V₁] [Fintype V₂] [Fintype W₁]
    [Fintype W₂] [DecidableEq V₁] [DecidableEq V₂] [DecidableEq W₁] [DecidableEq W₂]
    {A : SimpleGraph V₁} {A' : SimpleGraph W₁} {B : SimpleGraph V₂} {B' : SimpleGraph W₂}
    [DecidableRel A.Adj] [DecidableRel A'.Adj] [DecidableRel B.Adj] [DecidableRel B'.Adj]
    (e : A ≃g A') (f : B ≃g B') : strongProd A B ≃g strongProd A' B' where
  toEquiv := Equiv.prodCongr e.toEquiv f.toEquiv
  map_rel_iff' := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    show (strongProd A' B').Adj (e a₁, f b₁) (e a₂, f b₂) ↔ (strongProd A B).Adj (a₁, b₁) (a₂, b₂)
    rw [strongProd_adj, strongProd_adj]
    have hA : conflict A' (e a₁) (e a₂) ↔ conflict A a₁ a₂ := by
      constructor
      · rintro (h | h)
        · exact Or.inl (e.injective h)
        · exact Or.inr (e.map_rel_iff.mp h)
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr (e.map_rel_iff.mpr h)
    have hB : conflict B' (f b₁) (f b₂) ↔ conflict B b₁ b₂ := by
      constructor
      · rintro (h | h)
        · exact Or.inl (f.injective h)
        · exact Or.inr (f.map_rel_iff.mp h)
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr (f.map_rel_iff.mpr h)
    rw [hA, hB]
    constructor
    · rintro ⟨hne, h1, h2⟩
      refine ⟨fun heq => hne ?_, h1, h2⟩
      have ha : a₁ = a₂ := congrArg Prod.fst heq
      have hb : b₁ = b₂ := congrArg Prod.snd heq
      rw [ha, hb]
    · rintro ⟨hne, h1, h2⟩
      refine ⟨fun heq => hne ?_, h1, h2⟩
      have ha : e a₁ = e a₂ := congrArg Prod.fst heq
      have hb : f b₁ = f b₂ := congrArg Prod.snd heq
      exact Prod.ext (e.injective ha) (f.injective hb)

end ShannonBounds
