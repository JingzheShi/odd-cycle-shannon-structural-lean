import C7Improvement.C4AtomData

namespace ShannonBounds.C7Improvement

theorem C4_size_sum_check : (C4source.map fun piece =>
    (tenAtomSize piece.1.1 * (fiveAtomList piece.1.2).length) *
      (tenAtomSize piece.2.1 * (fiveAtomList piece.2.2).length)).sum = 2455726444728097 := by
  native_decide

end ShannonBounds.C7Improvement
