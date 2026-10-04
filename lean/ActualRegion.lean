import StarRegion
import PhysicalStar

namespace C13Structure
open Finset SimpleGraph ShannonBounds ShannonBounds.BaseC13

theorem physicalCode_independent_iff (f g h : H → Bool) :
    G6.IsIndepSet ↑(physicalCode f g h) ↔
      Compatible backX f g ∧ Compatible backY f h := by
  constructor
  · intro hi
    have forbid : ∀ u v : Index, u.1 ≠ v.1 → tagMask f g h u = true →
        tagMask f g h v = true → ¬StarConflict u v := by
      intro u v ht hu hv he
      have pu : physical u ∈ physicalCode f g h :=
        mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, hu⟩, rfl⟩
      have pv : physical v ∈ physicalCode f g h :=
        mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩, rfl⟩
      have ne : physical u ≠ physical v := by
        intro heq
        exact ht (congrArg Prod.fst (physical_injective heq))
      exact hi pu pv ne ⟨ne, (physical_conflict u v).mpr he⟩
    constructor
    · intro p hp
      have hp' : tagMask f g h (1,p) = true := by simpa [tagMask] using hp
      constructor
      · cases he : f p
        · rfl
        · exact False.elim (forbid (0,p) (1,p) (by simp) (by simpa [tagMask] using he)
            hp' (Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩)))
      · cases he : f (backX p)
        · rfl
        · exact False.elim (forbid (0,backX p) (1,p) (by simp) (by simpa [tagMask] using he)
            hp' (Or.inr (Or.inl ⟨rfl, rfl, Or.inr rfl⟩)))
    · intro p hp
      have hp' : tagMask f g h (2,p) = true := by simpa [tagMask] using hp
      constructor
      · cases he : f p
        · rfl
        · exact False.elim (forbid (0,p) (2,p) (by simp) (by simpa [tagMask] using he)
            hp' (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩)))))
      · cases he : f (backY p)
        · rfl
        · exact False.elim (forbid (0,backY p) (2,p) (by simp) (by simpa [tagMask] using he)
            hp' (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inr rfl⟩)))))
  · rintro ⟨hx,hy⟩
    exact physicalCode_independent f g h hx hy

def fiberCode (tag : Fin 3) (f : H → Bool) : Finset Code :=
  (pixels f).image (fun p => physical (tag,p))

theorem fiberCode_card (tag : Fin 3) (f : H → Bool) :
    (fiberCode tag f).card = (pixels f).card := by
  apply card_image_of_injective
  intro u v he
  exact congrArg Prod.snd (physical_injective he)

/-- The complete local feasibility theorem stated using actual physical graph
independence and actual finite fiber cardinalities, not hypothetical profiles. -/
theorem actual_star_region_iff (a b c : Nat)
    (hab : a + b ≤ 169) (hac : a + c ≤ 169)
    (hsx : 169 - a - b < 13) (hsy : 169 - a - c < 13) :
    (∃ f g h : H → Bool, G6.IsIndepSet ↑(physicalCode f g h) ∧
      (fiberCode 0 f).card = a ∧ b ≤ (fiberCode 1 g).card ∧ c ≤ (fiberCode 2 h).card) ↔
    (a ≤ (169 - a - c) * (169 - a - b) ∨
      169 - a ≤ (169 - a - c) * (169 - a - b)) := by
  simp only [physicalCode_independent_iff, fiberCode_card, and_assoc]
  exact star_region_iff a b c hab hac hsx hsy

theorem actual_star_upper80 (f g h : H → Bool)
    (hi : G6.IsIndepSet ↑(physicalCode f g h)) :
    (fiberCode 0 f).card ≤ 80 ∨ (fiberCode 1 g).card ≤ 80 ∨ (fiberCode 2 h).card ≤ 80 := by
  rcases (physicalCode_independent_iff f g h).mp hi with ⟨hx,hy⟩
  simpa only [fiberCode_card] using star_upper80 f g h hx hy

theorem actual_star_attains80 :
    G6.IsIndepSet ↑(physicalCode cornerMask xLeaf yLeaf) ∧
    (fiberCode 0 cornerMask).card = 80 ∧ (fiberCode 1 xLeaf).card = 80 ∧
    (fiberCode 2 yLeaf).card = 80 := by
  simpa only [fiberCode_card] using And.intro corner_physical_independent corner_sizes

end C13Structure
