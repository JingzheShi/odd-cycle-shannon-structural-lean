import VoltageStar
import ShannonBounds.CapC13

namespace C13Structure
open Finset SimpleGraph ShannonBounds ShannonBounds.BaseC13
abbrev Index := Fin 3 × H

/-- Three actual syndrome fibers 0, 2197, 2368. Leaf coordinates include the
common gauge translation (-1,0), so the normalized double voltages are {0,ex}
and {0,ey}. This is an injective map into the actual C13^6 vertex set. -/
def physical (u : Index) : Code :=
  let a := if u.1 = 0 then u.2.1.val else (u.2.1.val + 12) % 13
  let c := u.2.2.val
  let b := (2*a + if u.1 = 0 then 0 else 1) % 13
  let d := (13 - 2*c % 13 + if u.1 = 2 then 1 else 0) % 13
  let z := (a + if u.1 = 2 then 2 else 0) % 13
  ⟨mk6 a b c d 0 z % 4826809, Nat.mod_lt _ (by decide)⟩

def StarConflict (u v : Index) : Prop :=
  (u.1 = v.1 ∧ u.2 = v.2) ∨
  (u.1 = 0 ∧ v.1 = 1 ∧ (u.2 = v.2 ∨ u.2 = backX v.2)) ∨
  (u.1 = 1 ∧ v.1 = 0 ∧ (v.2 = u.2 ∨ v.2 = backX u.2)) ∨
  (u.1 = 0 ∧ v.1 = 2 ∧ (u.2 = v.2 ∨ u.2 = backY v.2)) ∨
  (u.1 = 2 ∧ v.1 = 0 ∧ (v.2 = u.2 ∨ v.2 = backY u.2))

theorem physical_injective : Function.Injective physical := by native_decide

/-- All 507^2 pairs, including same-fiber, leaf-leaf, and boundary pairs.
No quotient relation is substituted for actual physical graph adjacency. -/
theorem physical_conflict : ∀ u v : Index,
    wconf (physical u) (physical v) = true ↔ StarConflict u v := by
  unfold StarConflict
  native_decide

def tagMask (f g h : H → Bool) (u : Index) : Bool :=
  if u.1 = 0 then f u.2 else if u.1 = 1 then g u.2 else h u.2
def selected (f g h : H → Bool) : Finset Index :=
  univ.filter (fun u => tagMask f g h u = true)
def physicalCode (f g h : H → Bool) : Finset Code :=
  (selected f g h).image physical

theorem compatible_conflicts_equal (f g h : H → Bool)
    (hx : Compatible backX f g) (hy : Compatible backY f h)
    (u v : Index) (hu : tagMask f g h u = true) (hv : tagMask f g h v = true)
    (he : StarConflict u v) : u = v := by
  rcases he with he | he | he | he | he
  · exact Prod.ext he.1 he.2
  · have hf : f u.2 = true := by simpa [tagMask, he.1] using hu
    have hg : g v.2 = true := by simpa [tagMask, he.2.1] using hv
    have hn := hx v.2 hg
    rcases he.2.2 with e | e
    · rw [e, hn.1] at hf; contradiction
    · rw [e, hn.2] at hf; contradiction
  · have hf : f v.2 = true := by simpa [tagMask, he.2.1] using hv
    have hg : g u.2 = true := by simpa [tagMask, he.1] using hu
    have hn := hx u.2 hg
    rcases he.2.2 with e | e
    · rw [e, hn.1] at hf; contradiction
    · rw [e, hn.2] at hf; contradiction
  · have hf : f u.2 = true := by simpa [tagMask, he.1] using hu
    have hh : h v.2 = true := by simpa [tagMask, he.2.1] using hv
    have hn := hy v.2 hh
    rcases he.2.2 with e | e
    · rw [e, hn.1] at hf; contradiction
    · rw [e, hn.2] at hf; contradiction
  · have hf : f v.2 = true := by simpa [tagMask, he.2.1] using hv
    have hh : h u.2 = true := by simpa [tagMask, he.1] using hu
    have hn := hy u.2 hh
    rcases he.2.2 with e | e
    · rw [e, hn.1] at hf; contradiction
    · rw [e, hn.2] at hf; contradiction

/-- An unconditional constructor in the actual graph for every compatible
triple of masks, rather than a conditional numerical profile. -/
theorem physicalCode_independent (f g h : H → Bool)
    (hx : Compatible backX f g) (hy : Compatible backY f h) :
    G6.IsIndepSet ↑(physicalCode f g h) := by
  intro x hx' y hy' hne hadj
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hx'
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hy'
  have he := compatible_conflicts_equal f g h hx hy u v (mem_filter.mp hu).2
    (mem_filter.mp hv).2 ((physical_conflict u v).mp hadj.2)
  exact hne (congrArg physical he)

theorem corner_physical_card : (physicalCode cornerMask xLeaf yLeaf).card = 240 := by
  native_decide

theorem corner_physical_independent :
    G6.IsIndepSet ↑(physicalCode cornerMask xLeaf yLeaf) :=
  physicalCode_independent _ _ _ corner_compatible.1 corner_compatible.2

def cycleCode : Finset (Fin 6 → Fin 13) :=
  (physicalCode cornerMask xLeaf yLeaf).image CapC13.codeEquiv

theorem cycleCode_card : cycleCode.card = 240 := by
  rw [cycleCode, card_image_of_injective _ CapC13.codeEquiv.injective, corner_physical_card]

theorem cycleCode_independent :
    (strongPower (SimpleGraph.cycleGraph 13) 6).IsIndepSet ↑cycleCode := by
  rw [← CapC13.Cyc_eq_cycleGraph]
  intro x hx y hy hne hadj
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
  have huv : u ≠ v := fun h => hne (congrArg CapC13.codeEquiv h)
  exact corner_physical_independent hu hv huv (CapC13.G6_iso.map_rel_iff.mp hadj)

end C13Structure
