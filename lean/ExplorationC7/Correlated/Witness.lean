import ExplorationC7.Correlated.Geometry
import ShannonBounds.CycleC7

namespace ShannonBounds.ExplorationC7.Correlated

open SimpleGraph BaseC7

def firstPoint : Fin 7 → Fin 3 → Fin 7 :=
  ![![0, 0, 0], ![1, 2, 1], ![2, 4, 2], ![3, 6, 3],
    ![4, 1, 4], ![5, 5, 5], ![6, 3, 6]]

def secondPoint : Fin 7 → Fin 3 → Fin 7 :=
  ![![0, 0, 2], ![1, 1, 4], ![2, 2, 6], ![3, 4, 0],
    ![4, 3, 5], ![5, 6, 1], ![6, 5, 3]]

def first : Finset (Fin 3 → Fin 7) := Finset.univ.image firstPoint

def second : Finset (Fin 3 → Fin 7) := Finset.univ.image secondPoint

theorem first_separators : ∀ left right : Fin 7, left ≠ right →
    ∃ coordinate, ¬ conflict Cyc7 (firstPoint left coordinate) (firstPoint right coordinate) := by
  native_decide

theorem second_separators : ∀ left right : Fin 7, left ≠ right →
    ∃ coordinate, ¬ conflict Cyc7 (secondPoint left coordinate) (secondPoint right coordinate) := by
  native_decide

theorem cross_separators : ∀ left right : Fin 7,
    ∃ coordinate, ¬ conflict Cyc7 (firstPoint left coordinate) (secondPoint right coordinate) := by
  native_decide

theorem first_independent : (strongPower Cyc7 3).IsIndepSet ↑first :=
  coupling_independent firstPoint first_separators

theorem second_independent : (strongPower Cyc7 3).IsIndepSet ↑second :=
  coupling_independent secondPoint second_separators

theorem cross_separated : Sep (strongPower Cyc7 3) first second := by
  apply (sep_iff_pair_conditioned first second).mpr
  intro left leftMember right rightMember
  obtain ⟨leftIndex, _, rfl⟩ := Finset.mem_image.mp leftMember
  obtain ⟨rightIndex, _, rfl⟩ := Finset.mem_image.mp rightMember
  exact cross_separators leftIndex rightIndex

theorem margins_full : ∀ coordinate : Fin 3,
    first.image (fun point => point coordinate) = Finset.univ ∧
    second.image (fun point => point coordinate) = Finset.univ := by
  native_decide

def essentialFirst : Fin 3 → Fin 7 := ![0, 1, 0]

def essentialSecond : Fin 3 → Fin 7 := ![5, 0, 0]

theorem essential_check : ∀ coordinate : Fin 3,
    ¬ conflict Cyc7 (firstPoint (essentialFirst coordinate) coordinate)
      (secondPoint (essentialSecond coordinate) coordinate) ∧
    ∀ other, other ≠ coordinate →
      conflict Cyc7 (firstPoint (essentialFirst coordinate) other)
        (secondPoint (essentialSecond coordinate) other) := by
  native_decide

theorem all_coordinates_essential : ∀ coordinate : Fin 3,
    ∃ left ∈ first, ∃ right ∈ second,
      ∀ other, other ≠ coordinate → conflict Cyc7 (left other) (right other) := by
  intro coordinate
  refine ⟨firstPoint (essentialFirst coordinate), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
    secondPoint (essentialSecond coordinate), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
  exact (essential_check coordinate).2

theorem projected_separation_needs_three {m : ℕ} (restriction : Fin m → Fin 3)
    (separated : Sep (strongPower Cyc7 m)
      (first.image fun point index => point (restriction index))
      (second.image fun point index => point (restriction index))) : 3 ≤ m := by
  have surjective := separation_projection_requires_surjective first second all_coordinates_essential restriction separated
  have cardinality := Fintype.card_le_of_surjective restriction surjective
  simpa using cardinality

theorem no_margin_separator : ∀ coordinate : Fin 3,
    ¬ Sep Cyc7 (first.image fun point => point coordinate)
      (second.image fun point => point coordinate) := by
  intro coordinate separated
  rw [(margins_full coordinate).1, (margins_full coordinate).2] at separated
  exact separated 0 (Finset.mem_univ _) 0 (Finset.mem_univ _) (conflict_rfl _)

attribute [local irreducible] first second rectangle

theorem rectangular_hulls_not_separated :
    ¬ Sep (strongPower Cyc7 3) (rectangularHull first) (rectangularHull second) := by
  intro separated
  unfold rectangularHull at separated
  have coordinateSeparated := (sep_rectangles_iff
    (fun coordinate => first.image fun point => point coordinate)
    (fun coordinate => second.image fun point => point coordinate)).mp separated
  obtain ⟨coordinate, contradicts⟩ := coordinateSeparated
  exact no_margin_separator coordinate contradicts

theorem first_not_affine : ∀ multiplier shift : Fin 7, ∃ index : Fin 7,
    (firstPoint index 1).val ≠ (multiplier.val * index.val + shift.val) % 7 := by
  native_decide

theorem second_not_affine : ∀ multiplier shift : Fin 7, ∃ index : Fin 7,
    (secondPoint index 1).val ≠ (multiplier.val * index.val + shift.val) % 7 := by
  native_decide

theorem literal_cardinalities : first.card = 7 ∧ second.card = 7 ∧ (first ∪ second).card = 14 := by
  native_decide

def coupledPoints : Fin 2 → Finset (Fin 3 → Fin 7) := ![first, second]

def coupledSep (left right : Fin 2) : Bool := decide (left ≠ right)

def actual : Realisation (Fin 2) coupledSep (strongPower Cyc7 3) where
  P := coupledPoints
  hindep symbol := by
    fin_cases symbol
    · exact first_independent
    · exact second_independent
  hsep left right separated := by
    fin_cases left <;> fin_cases right
    · simp [coupledSep] at separated
    · exact cross_separated
    · intro leftPoint leftMember rightPoint rightMember conflicting
      exact cross_separated rightPoint rightMember leftPoint leftMember (conflict_symm conflicting)
    · simp [coupledSep] at separated

theorem actual_weights : ∀ symbol : Fin 2, actual.w symbol = 7 := by
  intro symbol
  fin_cases symbol
  · exact literal_cardinalities.1
  · exact literal_cardinalities.2.1

theorem actual_union_independent : (strongPower Cyc7 3).IsIndepSet ↑(first ∪ second) := by
  intro left leftMember right rightMember different adjacent
  rcases Finset.mem_union.mp leftMember with leftFirst | leftSecond
  · rcases Finset.mem_union.mp rightMember with rightFirst | rightSecond
    · exact first_independent leftFirst rightFirst different adjacent
    · exact cross_separated left leftFirst right rightSecond (Or.inr adjacent)
  · rcases Finset.mem_union.mp rightMember with rightFirst | rightSecond
    · exact cross_separated right rightFirst left leftSecond (conflict_symm (Or.inr adjacent))
    · exact second_independent leftSecond rightSecond different adjacent

theorem actual_fourteen : 14 ≤ (strongPower Cyc7 3).indepNum := by
  have cardinality := actual_union_independent.card_le_indepNum
  simpa only [literal_cardinalities.2.2] using cardinality

theorem illustrative_capacity_root : (14 : ℝ) ^ ((1 : ℝ) / 3) ≤ shannonCapacity Cyc7 := by
  calc
    _ ≤ ((strongPower Cyc7 3).indepNum : ℝ) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact_mod_cast actual_fourteen
    _ ≤ shannonCapacity Cyc7 := shannonCapacity_ge_root Cyc7 3 (by norm_num)

end ShannonBounds.ExplorationC7.Correlated
