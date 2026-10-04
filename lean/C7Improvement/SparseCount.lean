import C7Improvement.Histogram

namespace ShannonBounds.C7Improvement

open scoped BigOperators

variable {Left Right Key LeftKey RightKey : Type*}
variable [DecidableEq Left] [DecidableEq Right] [DecidableEq Key]
variable [DecidableEq LeftKey] [DecidableEq RightKey]

theorem image_product_tags (left : Finset Left) (right : Finset Right)
    (leftTag : Left → LeftKey) (rightTag : Right → RightKey) (merge : LeftKey → RightKey → Key) :
    (left ×ˢ right).image (fun point => merge (leftTag point.1) (rightTag point.2)) =
      ((left.image leftTag) ×ˢ (right.image rightTag)).image (fun keys => merge keys.1 keys.2) := by
  ext key
  constructor
  · rintro member
    obtain ⟨point, coordinates, equal⟩ := Finset.mem_image.mp member
    obtain ⟨memberLeft, memberRight⟩ := Finset.mem_product.mp coordinates
    exact Finset.mem_image.mpr ⟨(leftTag point.1, rightTag point.2),
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨point.1, memberLeft, rfl⟩,
        Finset.mem_image.mpr ⟨point.2, memberRight, rfl⟩⟩, equal⟩
  · rintro member
    obtain ⟨keys, coordinates, equal⟩ := Finset.mem_image.mp member
    obtain ⟨memberLeft, memberRight⟩ := Finset.mem_product.mp coordinates
    obtain ⟨first, memberFirst, sameFirst⟩ := Finset.mem_image.mp memberLeft
    obtain ⟨second, memberSecond, sameSecond⟩ := Finset.mem_image.mp memberRight
    refine Finset.mem_image.mpr ⟨(first, second), Finset.mem_product.mpr ⟨memberFirst, memberSecond⟩, ?_⟩
    simpa only [sameFirst, sameSecond] using equal

theorem histogram_sum_on (points : Finset Left) (tag : Left → LeftKey)
    (support : Finset LeftKey) (covers : ∀ point ∈ points, tag point ∈ support) (weight : LeftKey → ℕ) :
    (∑ point ∈ points, weight (tag point)) =
      ∑ key ∈ support, frequency points tag key * weight key := by
  simpa only [frequency, Finset.sum_const, smul_eq_mul] using
    (Finset.sum_fiberwise_of_maps_to' covers weight).symm

theorem histogram_product_sum_on (left : Finset Left) (right : Finset Right)
    (leftTag : Left → LeftKey) (rightTag : Right → RightKey)
    (leftSupport : Finset LeftKey) (rightSupport : Finset RightKey)
    (coversLeft : ∀ point ∈ left, leftTag point ∈ leftSupport)
    (coversRight : ∀ point ∈ right, rightTag point ∈ rightSupport)
    (merge : LeftKey → RightKey → Key) (weight : Key → ℕ) :
    (∑ point ∈ left ×ˢ right, weight (merge (leftTag point.1) (rightTag point.2))) =
      ∑ leftKey ∈ leftSupport, ∑ rightKey ∈ rightSupport,
        frequency left leftTag leftKey * frequency right rightTag rightKey *
          weight (merge leftKey rightKey) := by
  rw [Finset.sum_product, histogram_sum_on left leftTag leftSupport coversLeft
    (fun leftKey => ∑ point ∈ right, weight (merge leftKey (rightTag point)))]
  apply Finset.sum_congr rfl
  intro leftKey member
  rw [histogram_sum_on right rightTag rightSupport coversRight
    (fun rightKey => weight (merge leftKey rightKey)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rightKey memberRight
  exact (Nat.mul_assoc _ _ _).symm

theorem list_frequency_spec (points : List Left) (unique : points.Nodup)
    (tag : Left → LeftKey) (key : LeftKey) :
    frequency points.toFinset tag key = (points.filter fun point => tag point == key).length := by
  have equalFilters : points.toFinset.filter (fun point => tag point = key) =
      (points.filter fun point => tag point == key).toFinset := by
    ext point
    simp only [List.mem_toFinset, Finset.mem_filter, List.mem_filter, beq_iff_eq]
  rw [frequency, equalFilters, List.toFinset_card_of_nodup (unique.filter _)]

variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]

theorem count_outside_product_on {references : ℕ} (left : Finset Left) (right : Finset Right)
    (leftAtoms : Fin references → Finset Left) (rightAtoms : Fin references → Finset Right)
    (leftSupport rightSupport : Finset (Fin references → Bool))
    (coversLeft : ∀ point ∈ left, neighborhoodFlags (GL := GL) leftAtoms point ∈ leftSupport)
    (coversRight : ∀ point ∈ right, neighborhoodFlags (GL := GR) rightAtoms point ∈ rightSupport) :
    ((left ×ˢ right).filter fun point =>
      ¬ near (strongProd GL GR) (referenceUnion leftAtoms rightAtoms) point).card =
      ∑ leftFlags ∈ leftSupport, ∑ rightFlags ∈ rightSupport,
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
  rw [equalFilters, Finset.card_eq_sum_ones, Finset.sum_filter,
    histogram_product_sum_on left right (neighborhoodFlags (GL := GL) leftAtoms)
      (neighborhoodFlags (GL := GR) rightAtoms) leftSupport rightSupport coversLeft coversRight
      mergeFlags (fun flags => if ∀ index, flags index = false then 1 else 0)]
  apply Finset.sum_congr rfl
  intro leftFlags memberLeft
  apply Finset.sum_congr rfl
  intro rightFlags memberRight
  split_ifs <;> simp

end ShannonBounds.C7Improvement
