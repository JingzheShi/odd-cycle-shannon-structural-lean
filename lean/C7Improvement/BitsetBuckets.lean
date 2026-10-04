import Mathlib.Data.Nat.Bitwise
import C7Improvement.Automorphism

namespace ShannonBounds.C7Improvement

structure BitBuckets (dimension : ℕ) where
  data : Array ℕ
  size_eq : data.size = dimension

namespace BitBuckets

def empty (dimension : ℕ) : BitBuckets dimension :=
  ⟨Array.replicate dimension 0, by simp⟩

def add {dimension : ℕ} (buckets : BitBuckets dimension) (point : Fin dimension × Fin dimension) :
    BitBuckets dimension :=
  ⟨buckets.data.modify point.1.val (fun bits => bits ||| 2 ^ point.2.val), by
    simpa using buckets.size_eq⟩

def bit {dimension : ℕ} (buckets : BitBuckets dimension) (first second : Fin dimension) : Bool :=
  (buckets.data[first.val]'(by simpa only [buckets.size_eq] using first.isLt)).testBit second.val

theorem empty_bit (dimension : ℕ) (first second : Fin dimension) :
    (empty dimension).bit first second = false := by
  simp [empty, bit]

theorem add_bit {dimension : ℕ} (buckets : BitBuckets dimension)
    (point : Fin dimension × Fin dimension) (first second : Fin dimension) :
    (buckets.add point).bit first second = true ↔
      buckets.bit first second = true ∨ (first = point.1 ∧ second = point.2) := by
  unfold add bit
  rw [Array.getElem_modify]
  by_cases equalFirst : point.1.val = first.val
  · simp only [equalFirst, if_true, Nat.testBit_lor, Bool.or_eq_true,
      Nat.testBit_two_pow, decide_eq_true_eq]
    have firstEqual : first = point.1 := (Fin.ext equalFirst).symm
    simp only [firstEqual, true_and, Fin.ext_iff]
    exact or_congr Iff.rfl eq_comm
  · simp only [equalFirst, if_false]
    have firstUnequal : first ≠ point.1 := fun equal => equalFirst (congrArg Fin.val equal).symm
    simp only [firstUnequal, false_and, or_false]

theorem fold_bit {dimension : ℕ} (points : List (Fin dimension × Fin dimension))
    (buckets : BitBuckets dimension) (first second : Fin dimension) :
    (points.foldl add buckets).bit first second = true ↔
      buckets.bit first second = true ∨ (first, second) ∈ points := by
  induction points generalizing buckets with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, or_false]
  | cons point points inductionHypothesis =>
    rw [List.foldl_cons, inductionHypothesis, add_bit, List.mem_cons]
    simp only [Prod.ext_iff]
    tauto

end BitBuckets

def buildBuckets {dimension : ℕ} (points : List (Fin dimension × Fin dimension)) :
    BitBuckets dimension := points.foldl BitBuckets.add (BitBuckets.empty dimension)

theorem buildBuckets_spec {dimension : ℕ} (points : List (Fin dimension × Fin dimension))
    (first second : Fin dimension) :
    (buildBuckets points).bit first second = true ↔ (first, second) ∈ points := by
  rw [buildBuckets, BitBuckets.fold_bit, BitBuckets.empty_bit]
  simp

def bitUnion (values : List ℕ) : ℕ := values.foldr (fun first second => first ||| second) 0

theorem bitUnion_spec (values : List ℕ) (index : ℕ) :
    (bitUnion values).testBit index = true ↔ ∃ value ∈ values, value.testBit index = true := by
  induction values with
  | nil => simp [bitUnion]
  | cons value values inductionHypothesis =>
    change (value ||| bitUnion values).testBit index = true ↔ _
    simp only [Nat.testBit_lor, Bool.or_eq_true,
      inductionHypothesis, List.mem_cons, exists_eq_or_imp]

def listBits {dimension : ℕ} (points : List (Fin dimension)) : ℕ :=
  bitUnion (points.map fun point => 2 ^ point.val)

theorem listBits_spec {dimension : ℕ} (points : List (Fin dimension)) (index : ℕ) :
    (listBits points).testBit index = true ↔ ∃ point ∈ points, point.val = index := by
  simp only [listBits, bitUnion_spec, List.mem_map, Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · rintro ⟨value, ⟨point, member, rfl⟩, equal⟩
    exact ⟨point, member, by simpa only [Nat.testBit_two_pow, decide_eq_true_eq] using equal⟩
  · rintro ⟨point, member, equal⟩
    exact ⟨2 ^ point.val, ⟨point, member, rfl⟩, by
      simpa only [Nat.testBit_two_pow, decide_eq_true_eq] using equal⟩

theorem bit_intersection_nonzero (first second : ℕ) :
    first &&& second ≠ 0 ↔ ∃ index, first.testBit index = true ∧ second.testBit index = true := by
  constructor
  · intro nonzero
    by_contra noBit
    apply nonzero
    apply Nat.zero_of_testBit_eq_false
    intro index
    rw [Nat.testBit_land]
    apply Bool.eq_false_iff.mpr
    intro both
    have parsed : first.testBit index = true ∧ second.testBit index = true := by
      simpa only [Bool.and_eq_true] using both
    exact noBit ⟨index, parsed⟩
  · rintro ⟨index, firstTrue, secondTrue⟩ equalZero
    have equalBit := congrArg (fun value : ℕ => value.testBit index) equalZero
    simp only [Nat.testBit_land, firstTrue, secondTrue, Bool.and_true, Nat.zero_testBit] at equalBit
    contradiction

end ShannonBounds.C7Improvement
