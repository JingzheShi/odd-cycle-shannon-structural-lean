import VoltageStar

namespace C13Structure
open Finset

def freeMask (back : H → H) (f : H → Bool) (p : H) : Bool :=
  !f p && !f (back p)

theorem freeMask_compatible (back : H → H) (f : H → Bool) :
    Compatible back f (freeMask back f) := by
  intro p hp
  simpa [freeMask] using hp

theorem exact_dilation_budget (back : H → H) (f : H → Bool) :
    (pixels f).card + (univ.filter (fun p => f p = false ∧ f (back p) = true)).card
      + (pixels (freeMask back f)).card = 169 := by
  let b := univ.filter (fun p => f p = false ∧ f (back p) = true)
  have hab : Disjoint (pixels f) b := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2.1
    simp [hp'] at hq'
  have hac : Disjoint (pixels f) (pixels (freeMask back f)) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_filter.mp hp).2
    have hq' := (freeMask_compatible back f p (mem_filter.mp hq).2).1
    simp [hp'] at hq'
  have hbc : Disjoint b (pixels (freeMask back f)) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_filter.mp hp).2.2
    have hq' := (freeMask_compatible back f p (mem_filter.mp hq).2).2
    simp [hp'] at hq'
  have hu : pixels f ∪ b ∪ pixels (freeMask back f) = univ := by
    ext p
    cases hf : f p <;> cases hb : f (back p) <;> simp [pixels, b, freeMask, hf, hb]
  have hh := congrArg Finset.card hu
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hac, hbc⟩),
      card_union_of_disjoint hab] at hh
  simpa [b] using hh

/-- Row-major Ferrers diagram; parameters are at most 12 so neither direction
wraps around the torus. This is a reusable family, not a search table. -/
def ferrers (r c : Fin 13) (n : Fin 170) (p : H) : Bool :=
  decide (p.1.val < r.val ∧ p.2.val < c.val ∧ p.1.val * c.val + p.2.val < n.val)

/-- Bounded finite template verification: 13*13*170 parameter triples and
169 pixels each, not arbitrary-mask enumeration. Complement templates included. -/
theorem ferrers_statistics : ∀ r c : Fin 13, ∀ n : Fin 170,
    n.val ≤ r.val * c.val →
    (pixels (ferrers r c n)).card = n.val ∧
    (boundaryX (ferrers r c n)).card ≤ c.val ∧
    (boundaryY (ferrers r c n)).card ≤ r.val ∧
    (pixels (fun p => !ferrers r c n p)).card = 169 - n.val ∧
    (boundaryX (fun p => !ferrers r c n p)).card ≤ c.val ∧
    (boundaryY (fun p => !ferrers r c n p)).card ≤ r.val := by
  native_decide

/-- Exact Pareto feasibility in the small-directional-slack regime.
The center has exactly a points; the two leaves have at least b and c.
The theorem quantifies over all masks on the left, and supplies explicit
Ferrers/complement masks in the reverse implication. -/
theorem star_region_iff (a b c : Nat)
    (hab : a + b ≤ 169) (hac : a + c ≤ 169)
    (hsx : 169 - a - b < 13) (hsy : 169 - a - c < 13) :
    (∃ f g h : H → Bool, Compatible backX f g ∧ Compatible backY f h ∧
      (pixels f).card = a ∧ b ≤ (pixels g).card ∧ c ≤ (pixels h).card) ↔
    (a ≤ (169 - a - c) * (169 - a - b) ∨
      169 - a ≤ (169 - a - c) * (169 - a - b)) := by
  constructor
  · rintro ⟨f, g, h, hx, hy, ha, hb, hc⟩
    have dx := dilation_budget backX f g hx
    have dy := dilation_budget backY f h hy
    have bx : (boundaryX f).card ≤ 169 - a - b := by
      change (pixels f).card + (boundaryX f).card + (pixels g).card ≤ 169 at dx
      omega
    have byy : (boundaryY f).card ≤ 169 - a - c := by
      change (pixels f).card + (boundaryY f).card + (pixels h).card ≤ 169 at dy
      omega
    have prod := Nat.mul_le_mul byy bx
    have comp : (pixels (fun p => !f p)).card = 169 - a := by
      have hh := pixels_complement f
      have hh' : (pixels f).card + (pixels (fun p => !f p)).card = 169 := by simpa using hh
      omega
    rcases directional_minority_bound f (bx.trans_lt hsx) (byy.trans_lt hsy) with h | h
    · left
      have hh := h.trans prod
      rw [ha] at hh
      exact hh
    · right
      have hh := h.trans prod
      rw [comp] at hh
      exact hh
  · intro h
    let r : Fin 13 := ⟨169 - a - c, hsy⟩
    let s : Fin 13 := ⟨169 - a - b, hsx⟩
    have aa : a ≤ 169 := by omega
    have make : ∀ f : H → Bool, (pixels f).card = a →
        (boundaryX f).card ≤ s.val → (boundaryY f).card ≤ r.val →
        ∃ f g h : H → Bool, Compatible backX f g ∧ Compatible backY f h ∧
          (pixels f).card = a ∧ b ≤ (pixels g).card ∧ c ≤ (pixels h).card := by
      intro f ha hx hy
      refine ⟨f, freeMask backX f, freeMask backY f,
        freeMask_compatible _ _, freeMask_compatible _ _, ha, ?_, ?_⟩
      · have hh := exact_dilation_budget backX f
        change (pixels f).card + (boundaryX f).card + (pixels (freeMask backX f)).card = 169 at hh
        dsimp [s] at hx
        omega
      · have hh := exact_dilation_budget backY f
        change (pixels f).card + (boundaryY f).card + (pixels (freeMask backY f)).card = 169 at hh
        dsimp [r] at hy
        omega
    rcases h with h | h
    · let n : Fin 170 := ⟨a, by omega⟩
      have ht := ferrers_statistics r s n h
      exact make (ferrers r s n) ht.1 ht.2.1 ht.2.2.1
    · let n : Fin 170 := ⟨169 - a, by omega⟩
      have ht := ferrers_statistics r s n h
      apply make (fun p => !ferrers r s n p)
      · have hn : 169 - n.val = a := by dsimp [n]; omega
        exact ht.2.2.2.1.trans hn
      · exact ht.2.2.2.2.1
      · exact ht.2.2.2.2.2

end C13Structure
