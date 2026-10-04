import C7Improvement.FastNeighbors

namespace ShannonBounds.C7Improvement

structure PackedIndex (dimension : ℕ) where
  rows : Array ℕ
  neighbors : Array ℕ
  rows_size : rows.size = dimension
  neighbors_size : neighbors.size = dimension

def buildPackedIndex {dimension : ℕ} (neighbors : Fin dimension → List (Fin dimension))
    (points : List (Fin dimension × Fin dimension)) : PackedIndex dimension where
  rows := dilatedBuckets neighbors (buildBuckets points)
  neighbors := Array.ofFn fun point => listBits (neighbors point)
  rows_size := dilatedBuckets_size neighbors (buildBuckets points)
  neighbors_size := by simp

def PackedIndex.query {dimension : ℕ} (index : PackedIndex dimension)
    (point : Fin dimension × Fin dimension) : Bool :=
  (index.rows[point.1.val]'(by simpa only [index.rows_size] using point.1.isLt) &&&
    index.neighbors[point.2.val]'(by simpa only [index.neighbors_size] using point.2.isLt)) != 0

theorem buildPackedIndex_query {dimension : ℕ} (neighbors : Fin dimension → List (Fin dimension))
    (points : List (Fin dimension × Fin dimension)) (point : Fin dimension × Fin dimension) :
    (buildPackedIndex neighbors points).query point = packedNear neighbors points point := by
  simp only [PackedIndex.query, buildPackedIndex, Array.getElem_ofFn, packedNear, dilatedBit]

theorem packedIndex_graph_spec (points : List (BaseC7.Code × BaseC7.Code))
    (point : BaseC7.Code × BaseC7.Code) :
    (buildPackedIndex fastNeighbors5 points).query point = true ↔
      near (strongProd BaseC7.G5 BaseC7.G5) points.toFinset point := by
  rw [buildPackedIndex_query, packedNear_fast_spec]

end ShannonBounds.C7Improvement
