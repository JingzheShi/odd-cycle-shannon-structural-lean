import C7Improvement.Heterogeneous
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace ShannonBounds.C7Improvement

open scoped BigOperators

variable {Point Left Right Key LeftKey RightKey : Type*}
variable [DecidableEq Point] [DecidableEq Left] [DecidableEq Right]
variable [DecidableEq Key] [DecidableEq LeftKey] [DecidableEq RightKey]

def frequency (points : Finset Point) (tag : Point → Key) (key : Key) : ℕ :=
  (points.filter fun point => tag point = key).card

omit [DecidableEq Point] in
theorem histogram_sum (points : Finset Point) (tag : Point → Key) (weight : Key → ℕ) :
    (∑ point ∈ points, weight (tag point)) =
      ∑ key ∈ points.image tag, frequency points tag key * weight key := by
  have regroup := Finset.sum_fiberwise_of_maps_to' (s := points) (t := points.image tag)
    (g := tag) (fun point member => Finset.mem_image_of_mem tag member) weight
  simpa only [frequency, Finset.sum_const, smul_eq_mul] using regroup.symm

theorem histogram_filter (points : Finset Point) (tag : Point → Key)
    (accept : Key → Prop) [DecidablePred accept] :
    (points.filter fun point => accept (tag point)).card =
      ∑ key ∈ points.image tag, if accept key then frequency points tag key else 0 := by
  calc
    _ = ∑ point ∈ points, if accept (tag point) then 1 else 0 := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ key ∈ points.image tag,
        frequency points tag key * (if accept key then 1 else 0) :=
      histogram_sum points tag (fun key => if accept key then 1 else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro key member
      split_ifs <;> simp

omit [DecidableEq Key] in
theorem histogram_product_sum (left : Finset Left) (right : Finset Right)
    (leftTag : Left → LeftKey) (rightTag : Right → RightKey)
    (merge : LeftKey → RightKey → Key) (weight : Key → ℕ) :
    (∑ point ∈ left ×ˢ right, weight (merge (leftTag point.1) (rightTag point.2))) =
      ∑ leftKey ∈ left.image leftTag, ∑ rightKey ∈ right.image rightTag,
        frequency left leftTag leftKey * frequency right rightTag rightKey *
          weight (merge leftKey rightKey) := by
  rw [Finset.sum_product]
  rw [histogram_sum left leftTag
    (fun leftKey => ∑ point ∈ right, weight (merge leftKey (rightTag point)))]
  apply Finset.sum_congr rfl
  intro leftKey member
  rw [histogram_sum right rightTag (fun rightKey => weight (merge leftKey rightKey)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rightKey memberRight
  exact (Nat.mul_assoc _ _ _).symm

theorem histogram_product_frequency (left : Finset Left) (right : Finset Right)
    (leftTag : Left → LeftKey) (rightTag : Right → RightKey)
    (merge : LeftKey → RightKey → Key) (key : Key) :
    frequency (left ×ˢ right) (fun point => merge (leftTag point.1) (rightTag point.2)) key =
      ∑ leftKey ∈ left.image leftTag, ∑ rightKey ∈ right.image rightTag,
        if merge leftKey rightKey = key then
          frequency left leftTag leftKey * frequency right rightTag rightKey else 0 := by
  unfold frequency
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [histogram_product_sum left right leftTag rightTag merge
    (fun value => if value = key then 1 else 0)]
  apply Finset.sum_congr rfl
  intro leftKey memberLeft
  apply Finset.sum_congr rfl
  intro rightKey memberRight
  split_ifs <;> simp [frequency]

variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]

theorem near_product (left : Finset Left) (right : Finset Right) (point : Left × Right) :
    near (strongProd GL GR) (left ×ˢ right) point ↔
      near GL left point.1 ∧ near GR right point.2 := by
  constructor
  · rintro ⟨witness, member, confused⟩
    have coordinates := Finset.mem_product.mp member
    exact ⟨⟨witness.1, coordinates.1, (conflict_strongProd_iff.mp confused).1⟩,
      ⟨witness.2, coordinates.2, (conflict_strongProd_iff.mp confused).2⟩⟩
  · rintro ⟨⟨leftWitness, leftMember, leftConfused⟩, ⟨rightWitness, rightMember, rightConfused⟩⟩
    exact ⟨(leftWitness, rightWitness), Finset.mem_product.mpr ⟨leftMember, rightMember⟩,
      conflict_strongProd_iff.mpr ⟨leftConfused, rightConfused⟩⟩

theorem near_union (first second : Finset Left) (point : Left) :
    near GL (first ∪ second) point ↔ near GL first point ∨ near GL second point := by
  simp only [near, Finset.mem_union, or_and_right, exists_or]

def mergeFlags {references : ℕ} (left right : Fin references → Bool) : Fin references → Bool :=
  fun index => left index && right index

def neighborhoodFlags {references : ℕ} (atoms : Fin references → Finset Left)
    (point : Left) : Fin references → Bool :=
  fun index => decide (near GL (atoms index) point)

theorem merged_flags_spec {references : ℕ}
    (leftAtoms : Fin references → Finset Left) (rightAtoms : Fin references → Finset Right)
    (point : Left × Right) (index : Fin references) :
    mergeFlags (neighborhoodFlags (GL := GL) leftAtoms point.1)
      (neighborhoodFlags (GL := GR) rightAtoms point.2) index = true ↔
      near (strongProd GL GR) (leftAtoms index ×ˢ rightAtoms index) point := by
  simp only [mergeFlags, neighborhoodFlags, Bool.and_eq_true, decide_eq_true_eq, near_product]

def referenceUnion {references : ℕ} (leftAtoms : Fin references → Finset Left)
    (rightAtoms : Fin references → Finset Right) : Finset (Left × Right) :=
  Finset.univ.biUnion fun index => leftAtoms index ×ˢ rightAtoms index

theorem near_referenceUnion {references : ℕ}
    (leftAtoms : Fin references → Finset Left) (rightAtoms : Fin references → Finset Right)
    (point : Left × Right) :
    near (strongProd GL GR) (referenceUnion leftAtoms rightAtoms) point ↔
      ∃ index, near (strongProd GL GR) (leftAtoms index ×ˢ rightAtoms index) point := by
  constructor
  · rintro ⟨witness, member, confused⟩
    obtain ⟨index, _, memberBlock⟩ := Finset.mem_biUnion.mp member
    exact ⟨index, witness, memberBlock, confused⟩
  · rintro ⟨index, witness, memberBlock, confused⟩
    exact ⟨witness, Finset.mem_biUnion.mpr ⟨index, Finset.mem_univ index, memberBlock⟩, confused⟩

theorem outside_flags_spec {references : ℕ}
    (leftAtoms : Fin references → Finset Left) (rightAtoms : Fin references → Finset Right)
    (point : Left × Right) :
    ¬ near (strongProd GL GR) (referenceUnion leftAtoms rightAtoms) point ↔
      ∀ index, mergeFlags (neighborhoodFlags (GL := GL) leftAtoms point.1)
        (neighborhoodFlags (GL := GR) rightAtoms point.2) index = false := by
  rw [near_referenceUnion]
  constructor
  · intro outsideReference index
    cases flag : mergeFlags (neighborhoodFlags (GL := GL) leftAtoms point.1)
        (neighborhoodFlags (GL := GR) rightAtoms point.2) index with
    | false => rfl
    | true => exact False.elim (outsideReference ⟨index,
        (merged_flags_spec leftAtoms rightAtoms point index).mp flag⟩)
  · intro allFalse
    rintro ⟨index, nearby⟩
    have flag := (merged_flags_spec leftAtoms rightAtoms point index).mpr nearby
    rw [allFalse index] at flag
    cases flag

theorem count_outside_product {references : ℕ} (left : Finset Left) (right : Finset Right)
    (leftAtoms : Fin references → Finset Left) (rightAtoms : Fin references → Finset Right) :
    ((left ×ˢ right).filter fun point =>
      ¬ near (strongProd GL GR) (referenceUnion leftAtoms rightAtoms) point).card =
      ∑ leftFlags ∈ left.image (neighborhoodFlags (GL := GL) leftAtoms),
        ∑ rightFlags ∈ right.image (neighborhoodFlags (GL := GR) rightAtoms),
          if ∀ index, mergeFlags leftFlags rightFlags index = false then
            frequency left (neighborhoodFlags (GL := GL) leftAtoms) leftFlags *
            frequency right (neighborhoodFlags (GL := GR) rightAtoms) rightFlags else 0 := by
  have equalFilters :
      (left ×ˢ right).filter (fun point =>
        ¬ near (strongProd GL GR) (referenceUnion leftAtoms rightAtoms) point) =
      (left ×ˢ right).filter (fun point =>
        ∀ index, mergeFlags (neighborhoodFlags (GL := GL) leftAtoms point.1)
          (neighborhoodFlags (GL := GR) rightAtoms point.2) index = false) := by
    ext point
    simp only [Finset.mem_filter, outside_flags_spec]
  rw [equalFilters, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [histogram_product_sum left right
    (neighborhoodFlags (GL := GL) leftAtoms) (neighborhoodFlags (GL := GR) rightAtoms)
    mergeFlags (fun flags => if ∀ index, flags index = false then 1 else 0)]
  apply Finset.sum_congr rfl
  intro leftFlags memberLeft
  apply Finset.sum_congr rfl
  intro rightFlags memberRight
  split_ifs <;> simp

end ShannonBounds.C7Improvement
