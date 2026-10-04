import ShannonBounds.Layered
import Mathlib.Data.List.FinRange

namespace ShannonBounds.ExplorationC13FrontierR03.ListChecks

variable {X : Type*} [DecidableEq X]

def inside (rel : X → X → Bool) (xs : List X) : Bool :=
  xs.all fun x => xs.all fun y => decide (x = y) || rel x y

def between (rel : X → X → Bool) (xs ys : List X) : Bool :=
  xs.all fun x => ys.all fun y => rel x y

theorem of_inside {rel : X → X → Bool} {xs : List X}
    (h : inside rel xs = true) {x y : X} (hx : x ∈ xs.toFinset)
    (hy : y ∈ xs.toFinset) (hne : x ≠ y) : rel x y = true := by
  have hx' : x ∈ xs := List.mem_toFinset.mp hx
  have hy' : y ∈ xs := List.mem_toFinset.mp hy
  have hxy := List.all_eq_true.mp (List.all_eq_true.mp h x hx') y hy'
  have hxye : x = y ∨ rel x y = true := by simpa using hxy
  rcases hxye with he | hr
  · exact False.elim (hne he)
  · exact hr

theorem of_between {rel : X → X → Bool} {xs ys : List X}
    (h : between rel xs ys = true) {x y : X}
    (hx : x ∈ xs.toFinset) (hy : y ∈ ys.toFinset) : rel x y = true := by
  exact List.all_eq_true.mp
    (List.all_eq_true.mp h x (List.mem_toFinset.mp hx)) y (List.mem_toFinset.mp hy)

variable {A : Type*} [Fintype A] [DecidableEq A]

def wordApart (sep : A → A → Bool) {q : ℕ} (x y : Fin q → A) : Bool :=
  (List.finRange q).any fun i => sep (x i) (y i)

omit [Fintype A] [DecidableEq A] in
theorem wordApart_iff {sep : A → A → Bool} {q : ℕ} {x y : Fin q → A} :
    wordApart sep x y = true ↔ ∃ i, sep (x i) (y i) = true := by
  simp [wordApart, List.any_eq_true]

def substFromLists (sep : A → A → Bool) {q : ℕ}
    (rows : A → List (Fin q → A))
    (hin : ∀ a, inside (wordApart sep) (rows a) = true)
    (hcross : ∀ a b, sep a b = true → between (wordApart sep) (rows a) (rows b) = true) :
    Subst A sep q where
  T a := (rows a).toFinset
  hin := by
    intro a x hx y hy hne
    exact wordApart_iff.mp (of_inside (hin a) hx hy hne)
  hcross := by
    intro a b hab x hx y hy
    exact wordApart_iff.mp (of_between (hcross a b hab) hx hy)

def codeFromList (sep : A → A → Bool) {q : ℕ}
    (rows : List (Fin q → A))
    (h : inside (wordApart sep) rows = true) : Code A sep q where
  C := rows.toFinset
  hsep := by
    intro x hx y hy hne
    exact wordApart_iff.mp (of_inside h hx hy hne)


end ShannonBounds.ExplorationC13FrontierR03.ListChecks
