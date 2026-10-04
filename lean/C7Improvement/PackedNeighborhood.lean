import C7Improvement.BitsetBuckets
import C7Improvement.Histogram

namespace ShannonBounds.C7Improvement

def dilatedBuckets {dimension : ℕ} (neighbors : Fin dimension → List (Fin dimension))
    (buckets : BitBuckets dimension) : Array ℕ := Array.ofFn fun point =>
  bitUnion ((neighbors point).map fun neighbor =>
    buckets.data[neighbor.val]'(by simpa only [buckets.size_eq] using neighbor.isLt))

theorem dilatedBuckets_size {dimension : ℕ} (neighbors : Fin dimension → List (Fin dimension))
    (buckets : BitBuckets dimension) : (dilatedBuckets neighbors buckets).size = dimension := by
  simp [dilatedBuckets]

def dilatedBit {dimension : ℕ} (neighbors : Fin dimension → List (Fin dimension))
    (buckets : BitBuckets dimension) (point : Fin dimension) : ℕ :=
  (dilatedBuckets neighbors buckets)[point.val]'(by
    simpa only [dilatedBuckets_size] using point.isLt)

theorem dilatedBit_spec {dimension : ℕ} (neighbors : Fin dimension → List (Fin dimension))
    (points : List (Fin dimension × Fin dimension)) (first second : Fin dimension) :
    (dilatedBit neighbors (buildBuckets points) first).testBit second.val = true ↔
      ∃ neighbor ∈ neighbors first, (neighbor, second) ∈ points := by
  simp only [dilatedBit, dilatedBuckets, Array.getElem_ofFn]
  rw [bitUnion_spec]
  simp only [List.mem_map]
  constructor
  · rintro ⟨bits, ⟨neighbor, member, rfl⟩, bitTrue⟩
    exact ⟨neighbor, member, (buildBuckets_spec points neighbor second).mp bitTrue⟩
  · rintro ⟨neighbor, member, pairMember⟩
    exact ⟨_, ⟨neighbor, member, rfl⟩, (buildBuckets_spec points neighbor second).mpr pairMember⟩

def packedNear {dimension : ℕ} (neighbors : Fin dimension → List (Fin dimension))
    (points : List (Fin dimension × Fin dimension)) (point : Fin dimension × Fin dimension) : Bool :=
  (dilatedBit neighbors (buildBuckets points) point.1 &&& listBits (neighbors point.2)) != 0

theorem packedNear_spec {dimension : ℕ} (neighbors : Fin dimension → List (Fin dimension))
    (points : List (Fin dimension × Fin dimension)) (point : Fin dimension × Fin dimension) :
    packedNear neighbors points point = true ↔
      ∃ first ∈ neighbors point.1, ∃ second ∈ neighbors point.2, (first, second) ∈ points := by
  rw [packedNear, bne_iff_ne, bit_intersection_nonzero]
  constructor
  · rintro ⟨index, firstBit, secondBit⟩
    obtain ⟨second, memberSecond, equalIndex⟩ := (listBits_spec _ index).mp secondBit
    rw [← equalIndex] at firstBit
    obtain ⟨first, memberFirst, memberPair⟩ := (dilatedBit_spec neighbors points point.1 second).mp firstBit
    exact ⟨first, memberFirst, second, memberSecond, memberPair⟩
  · rintro ⟨first, memberFirst, second, memberSecond, memberPair⟩
    exact ⟨second.val,
      (dilatedBit_spec neighbors points point.1 second).mpr ⟨first, memberFirst, memberPair⟩,
      (listBits_spec _ second.val).mpr ⟨second, memberSecond, rfl⟩⟩

open BaseC7

def neighbors5 (point : BaseC7.Code) : List BaseC7.Code :=
  (List.finRange 16807).filter (wconf point)

theorem neighbors5_spec (point neighbor : BaseC7.Code) :
    neighbor ∈ neighbors5 point ↔ conflict G5 point neighbor := by
  simp only [neighbors5, List.mem_filter, List.mem_finRange, true_and, conflict_G5]

theorem packedNear_graph_spec (points : List (BaseC7.Code × BaseC7.Code))
    (point : BaseC7.Code × BaseC7.Code) :
    packedNear neighbors5 points point = true ↔ near (strongProd G5 G5) points.toFinset point := by
  rw [packedNear_spec]
  simp only [neighbors5_spec, near, List.mem_toFinset, conflict_strongProd_iff]
  constructor
  · rintro ⟨first, firstConflict, second, secondConflict, member⟩
    exact ⟨(first, second), member, firstConflict, secondConflict⟩
  · rintro ⟨witness, member, firstConflict, secondConflict⟩
    exact ⟨witness.1, firstConflict, witness.2, secondConflict, member⟩

end ShannonBounds.C7Improvement
