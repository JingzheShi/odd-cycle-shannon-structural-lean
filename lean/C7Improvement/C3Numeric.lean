import C7Improvement.C3Data

namespace ShannonBounds.C7Improvement

theorem C3_sum_check : blockOutsideCount X10List (baseAtom .N) +
    blockOutsideCount JplusList (baseAtom .D) +
    blockOutsideCount JplusList (baseAtom .A) = 14045805 := by
  native_decide

end ShannonBounds.C7Improvement
