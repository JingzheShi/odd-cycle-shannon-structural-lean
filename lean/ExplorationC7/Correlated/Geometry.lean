import ShannonBounds.Layered
import ShannonBounds.Flatten

namespace ShannonBounds.ExplorationC7.Correlated

open SimpleGraph

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def rectangle {q : ℕ} (pieces : Fin q → Finset V) : Finset (Fin q → V) :=
  Fintype.piFinset pieces

def rectangularHull {q : ℕ} (points : Finset (Fin q → V)) : Finset (Fin q → V) :=
  rectangle fun coordinate => points.image fun point => point coordinate

theorem sep_iff_pair_conditioned {q : ℕ} (first second : Finset (Fin q → V)) :
    Sep (strongPower G q) first second ↔
      ∀ left ∈ first, ∀ right ∈ second, ∃ coordinate, ¬ conflict G (left coordinate) (right coordinate) := by
  classical
  constructor
  · intro separated left leftMember right rightMember
    by_contra absent
    have every : ∀ coordinate, conflict G (left coordinate) (right coordinate) := by
      intro coordinate
      by_contra notConflicting
      exact absent ⟨coordinate, notConflicting⟩
    exact separated left leftMember right rightMember ((conflict_strongPower left right).mpr every)
  · intro routed left leftMember right rightMember conflicting
    obtain ⟨coordinate, separated⟩ := routed left leftMember right rightMember
    exact separated ((conflict_strongPower left right).mp conflicting coordinate)

theorem sep_rectangles_iff {q : ℕ} (first second : Fin q → Finset V) :
    Sep (strongPower G q) (rectangle first) (rectangle second) ↔
      ∃ coordinate, Sep G (first coordinate) (second coordinate) := by
  classical
  constructor
  · intro separated
    by_contra absent
    have witnesses : ∀ coordinate, ∃ left ∈ first coordinate,
        ∃ right ∈ second coordinate, conflict G left right := by
      intro coordinate
      have notSeparated : ¬ Sep G (first coordinate) (second coordinate) := by
        intro coordinateSeparated
        exact absent ⟨coordinate, coordinateSeparated⟩
      by_contra noWitness
      apply notSeparated
      intro left leftMember right rightMember conflicting
      exact noWitness ⟨left, leftMember, right, rightMember, conflicting⟩
    choose left leftMember right rightMember conflicting using witnesses
    exact separated left (by simpa [rectangle] using leftMember)
      right (by simpa [rectangle] using rightMember)
      ((conflict_strongPower left right).mpr conflicting)
  · rintro ⟨coordinate, separated⟩ left leftMember right rightMember conflicting
    have leftCoordinates : ∀ index, left index ∈ first index := by
      simpa [rectangle] using leftMember
    have rightCoordinates : ∀ index, right index ∈ second index := by
      simpa [rectangle] using rightMember
    exact separated (left coordinate) (leftCoordinates coordinate)
      (right coordinate) (rightCoordinates coordinate)
      ((conflict_strongPower left right).mp conflicting coordinate)

theorem mem_rectangularHull {q : ℕ} {points : Finset (Fin q → V)}
    {point : Fin q → V} (member : point ∈ points) : point ∈ rectangularHull points := by
  simp only [rectangularHull, rectangle, Fintype.mem_piFinset]
  intro coordinate
  exact Finset.mem_image.mpr ⟨point, member, rfl⟩

theorem coupling_independent {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}
    (rows : I → Fin q → V)
    (separators : ∀ first second, first ≠ second →
      ∃ coordinate, ¬ conflict G (rows first coordinate) (rows second coordinate)) :
    (strongPower G q).IsIndepSet ↑(Finset.univ.image rows) := by
  intro left leftMember right rightMember different adjacent
  obtain ⟨first, _, rfl⟩ := Finset.mem_image.mp leftMember
  obtain ⟨second, _, rfl⟩ := Finset.mem_image.mp rightMember
  have indicesDifferent : first ≠ second := fun equal => different (congrArg rows equal)
  obtain ⟨coordinate, separated⟩ := separators first second indicesDifferent
  exact separated (adjacent.2 coordinate)

theorem coupling_cardinality {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}
    (rows : I → Fin q → V)
    (separators : ∀ first second, first ≠ second →
      ∃ coordinate, ¬ conflict G (rows first coordinate) (rows second coordinate)) :
    (Finset.univ.image rows).card = Fintype.card I := by
  have injective : Function.Injective rows := by
    intro first second equal
    by_contra different
    obtain ⟨coordinate, separated⟩ := separators first second different
    exact separated (Or.inl (congrFun equal coordinate))
  rw [Finset.card_image_of_injective _ injective, Finset.card_univ]

theorem coupling_lower_bound [Fintype V] {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}
    (rows : I → Fin q → V)
    (separators : ∀ first second, first ≠ second →
      ∃ coordinate, ¬ conflict G (rows first coordinate) (rows second coordinate)) :
    Fintype.card I ≤ (strongPower G q).indepNum := by
  have bound := (coupling_independent rows separators).card_le_indepNum
  rw [coupling_cardinality rows separators] at bound
  exact bound

theorem coupling_gain [Fintype V] {I : Type*} [Fintype I] [DecidableEq I] {q threshold : ℕ}
    (rows : I → Fin q → V)
    (separators : ∀ first second, first ≠ second →
      ∃ coordinate, ¬ conflict G (rows first coordinate) (rows second coordinate))
    (gain : threshold < Fintype.card I) : threshold < (strongPower G q).indepNum :=
  lt_of_lt_of_le gain (coupling_lower_bound rows separators)

theorem separation_projection_requires_surjective {q m : ℕ}
    (first second : Finset (Fin q → V))
    (essential : ∀ coordinate, ∃ left ∈ first, ∃ right ∈ second,
      ∀ other, other ≠ coordinate → conflict G (left other) (right other))
    (restriction : Fin m → Fin q)
    (separated : Sep (strongPower G m)
      (first.image fun point index => point (restriction index))
      (second.image fun point index => point (restriction index))) :
    Function.Surjective restriction := by
  classical
  intro coordinate
  by_contra absent
  have avoids : ∀ index, restriction index ≠ coordinate := by
    intro index equality
    exact absent ⟨index, equality⟩
  obtain ⟨left, leftMember, right, rightMember, conflicting⟩ := essential coordinate
  exact separated (fun index => left (restriction index))
    (Finset.mem_image.mpr ⟨left, leftMember, rfl⟩)
    (fun index => right (restriction index))
    (Finset.mem_image.mpr ⟨right, rightMember, rfl⟩)
    ((conflict_strongPower _ _).mpr fun index => conflicting _ (avoids index))

end ShannonBounds.ExplorationC7.Correlated
