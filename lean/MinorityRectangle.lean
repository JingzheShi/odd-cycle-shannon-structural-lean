import Mathlib.Tactic

/-! A two-dimensional minority-rectangle lemma. This is purely combinatorial:
no graph profile, search outcome, or finite native premise is assumed. -/
namespace C13Structure
open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def pixels (f : X × Y → Bool) : Finset (X × Y) := univ.filter (fun p => f p = true)
def mixedRows (f : X × Y → Bool) : Finset X :=
  univ.filter (fun x => ∃ y z, f (x,y) ≠ f (x,z))
def mixedCols (f : X × Y → Bool) : Finset Y :=
  univ.filter (fun y => ∃ x z, f (x,y) ≠ f (z,y))

theorem minority_rectangle (f : X × Y → Bool)
    (hr : (mixedRows f).card < Fintype.card X)
    (hc : (mixedCols f).card < Fintype.card Y) :
    (pixels f).card ≤ (mixedRows f).card * (mixedCols f).card ∨
    (pixels (fun p => !f p)).card ≤ (mixedRows f).card * (mixedCols f).card := by
  obtain ⟨x₀, -, hx₀⟩ := exists_mem_notMem_of_card_lt_card (t := univ) (by simpa using hr)
  obtain ⟨y₀, -, hy₀⟩ := exists_mem_notMem_of_card_lt_card (t := univ) (by simpa using hc)
  have row : ∀ y z, f (x₀,y) = f (x₀,z) := by
    intro y z
    by_contra h
    exact hx₀ (mem_filter.mpr ⟨mem_univ _, y, z, h⟩)
  have col : ∀ x z, f (x,y₀) = f (z,y₀) := by
    intro x z
    by_contra h
    exact hy₀ (mem_filter.mpr ⟨mem_univ _, x, z, h⟩)
  have sub : ∀ p : X × Y, f p ≠ f (x₀,y₀) →
      p ∈ (mixedRows f) ×ˢ (mixedCols f) := by
    rintro ⟨x,y⟩ h
    apply mem_product.mpr
    constructor
    · apply mem_filter.mpr
      refine ⟨mem_univ _, y, y₀, ?_⟩
      simpa only [col x x₀] using h
    · apply mem_filter.mpr
      refine ⟨mem_univ _, x, x₀, ?_⟩
      simpa only [row y y₀] using h
  cases hb : f (x₀,y₀) with
  | false =>
    left
    calc
      (pixels f).card ≤ ((mixedRows f) ×ˢ (mixedCols f)).card := by
        apply card_le_card
        intro p hp
        apply sub p
        have hp' := (mem_filter.mp hp).2
        simp [hp', hb]
      _ = _ := card_product _ _
  | true =>
    right
    calc
      (pixels (fun p => !f p)).card ≤ ((mixedRows f) ×ˢ (mixedCols f)).card := by
        apply card_le_card
        intro p hp
        apply sub p
        have hp' : f p = false := by simpa using (mem_filter.mp hp).2
        simp [hp', hb]
      _ = _ := card_product _ _

theorem pixels_complement (f : X × Y → Bool) :
    (pixels f).card + (pixels (fun p => !f p)).card = Fintype.card (X × Y) := by
  have hd : Disjoint (pixels f) (pixels (fun p => !f p)) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    simp [hp'] at hq'
  have hu : pixels f ∪ pixels (fun p => !f p) = univ := by
    ext p
    cases h : f p <;> simp [pixels, h]
  rw [← card_union_of_disjoint hd, hu, card_univ]

end C13Structure
