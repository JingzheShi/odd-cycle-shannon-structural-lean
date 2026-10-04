import MinorityRectangle

namespace C13Structure
open Finset
abbrev F13 := Fin 13
abbrev H := F13 × F13
def prev (i : F13) : F13 := i + 12
def backX (p : H) : H := (prev p.1, p.2)
def backY (p : H) : H := (p.1, prev p.2)
def boundaryX (f : H → Bool) : Finset H :=
  univ.filter (fun p => f p = false ∧ f (backX p) = true)
def boundaryY (f : H → Bool) : Finset H :=
  univ.filter (fun p => f p = false ∧ f (backY p) = true)

/-- An 8192-row finite lemma, independent of any 169-point mask enumeration. -/
theorem cycle_transition : ∀ f : F13 → Bool,
    (∃ i j, f i ≠ f j) → ∃ i, f i = false ∧ f (prev i) = true := by
  native_decide

theorem mixedCols_le_boundaryX (f : H → Bool) :
    (mixedCols f).card ≤ (boundaryX f).card := by
  have hs : mixedCols f ⊆ (boundaryX f).image Prod.snd := by
    intro y hy
    have hy' : ∃ x z, f (x,y) ≠ f (z,y) := by simpa only [mixedCols, mem_filter, mem_univ, true_and] using hy
    obtain ⟨x, hx⟩ := cycle_transition (fun x => f (x,y)) hy'
    exact mem_image.mpr ⟨(x,y), mem_filter.mpr ⟨mem_univ _, hx⟩, rfl⟩
  exact (card_le_card hs).trans (card_image_le)

theorem mixedRows_le_boundaryY (f : H → Bool) :
    (mixedRows f).card ≤ (boundaryY f).card := by
  have hs : mixedRows f ⊆ (boundaryY f).image Prod.fst := by
    intro x hx
    have hx' : ∃ y z, f (x,y) ≠ f (x,z) := by simpa only [mixedRows, mem_filter, mem_univ, true_and] using hx
    obtain ⟨y, hy⟩ := cycle_transition (fun y => f (x,y)) hx'
    exact mem_image.mpr ⟨(x,y), mem_filter.mpr ⟨mem_univ _, hy⟩, rfl⟩
  exact (card_le_card hs).trans (card_image_le)

/-- New scope beyond the saturated stripe class: arbitrary Boolean masks. -/
theorem directional_minority_bound (f : H → Bool)
    (hx : (boundaryX f).card < 13) (hy : (boundaryY f).card < 13) :
    (pixels f).card ≤ (boundaryY f).card * (boundaryX f).card ∨
    (pixels (fun p => !f p)).card ≤ (boundaryY f).card * (boundaryX f).card := by
  have hr := mixedRows_le_boundaryY f
  have hc := mixedCols_le_boundaryX f
  have hm := Nat.mul_le_mul hr hc
  rcases minority_rectangle f (by simpa using hr.trans_lt hy)
      (by simpa using hc.trans_lt hx) with h | h
  · exact Or.inl (h.trans hm)
  · exact Or.inr (h.trans hm)

def Compatible (back : H → H) (f g : H → Bool) : Prop :=
  ∀ p, g p = true → f p = false ∧ f (back p) = false

theorem three_disjoint_bound (a b c : Finset H)
    (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) :
    a.card + b.card + c.card ≤ 169 := by
  have hh : (a ∪ b ∪ c).card ≤ (univ : Finset H).card := card_le_card (subset_univ _)
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hac, hbc⟩),
      card_union_of_disjoint hab] at hh
  simpa using hh

theorem dilation_budget (back : H → H) (f g : H → Bool)
    (h : Compatible back f g) :
    (pixels f).card + (univ.filter (fun p => f p = false ∧ f (back p) = true)).card
      + (pixels g).card ≤ 169 := by
  apply three_disjoint_bound
  · apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2.1
    simp [hp'] at hq'
  · apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_filter.mp hp).2
    have hq' := (h p (mem_filter.mp hq).2).1
    simp [hp'] at hq'
  · apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_filter.mp hp).2.2
    have hq' := (h p (mem_filter.mp hq).2).2
    simp [hp'] at hq'

/-- No assumptions on the shapes of the three masks. At least one has size ≤80. -/
theorem star_upper80 (f g h : H → Bool)
    (hx : Compatible backX f g) (hy : Compatible backY f h) :
    (pixels f).card ≤ 80 ∨ (pixels g).card ≤ 80 ∨ (pixels h).card ≤ 80 := by
  by_contra! hn
  have hbX : (pixels f).card + (boundaryX f).card + (pixels g).card ≤ 169 :=
    dilation_budget backX f g hx
  have hbY : (pixels f).card + (boundaryY f).card + (pixels h).card ≤ 169 :=
    dilation_budget backY f h hy
  have bx : (boundaryX f).card ≤ 7 := by omega
  have byy : (boundaryY f).card ≤ 7 := by omega
  have prod : (boundaryY f).card * (boundaryX f).card ≤ 49 := by
    exact (Nat.mul_le_mul byy bx)
  have hc := pixels_complement f
  have hc' : (pixels f).card + (pixels (fun p => !f p)).card = 169 := by simpa using hc
  rcases directional_minority_bound f (by omega) (by omega) with ha | ha <;> omega

def cornerMask (p : H) : Bool :=
  decide (p.1.val < 9 ∧ p.2.val < 9 ∧ ¬(p.1.val = 8 ∧ p.2.val = 8))
def xLeaf (p : H) : Bool := !cornerMask p && !cornerMask (backX p)
def yLeaf (p : H) : Bool := !cornerMask p && !cornerMask (backY p)

theorem corner_sizes : (pixels cornerMask).card = 80 ∧
    (pixels xLeaf).card = 80 ∧ (pixels yLeaf).card = 80 := by native_decide
theorem corner_compatible : Compatible backX cornerMask xLeaf ∧
    Compatible backY cornerMask yLeaf := by
  constructor
  · intro p hp
    simpa [xLeaf] using hp
  · intro p hp
    simpa [yLeaf] using hp

/-- Sharp equality: 80 is attainable, while 81 at all three vertices is impossible. -/
theorem balanced_star_exact :
    (∃ f g h : H → Bool, Compatible backX f g ∧ Compatible backY f h ∧
      (pixels f).card = 80 ∧ (pixels g).card = 80 ∧ (pixels h).card = 80) ∧
    (∀ f g h : H → Bool, Compatible backX f g → Compatible backY f h →
      (pixels f).card ≤ 80 ∨ (pixels g).card ≤ 80 ∨ (pixels h).card ≤ 80) := by
  exact ⟨⟨cornerMask, xLeaf, yLeaf, corner_compatible.1, corner_compatible.2,
      corner_sizes⟩, star_upper80⟩

end C13Structure
