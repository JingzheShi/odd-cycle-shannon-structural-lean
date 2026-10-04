import C7Improvement.Atoms10Data

namespace ShannonBounds.C7Improvement

def transformed10Atom (letter : Letter) := (atom10 letter).map transformPair

def transformed5Atom (letter : Letter) := (baseAtom letter).map transform

theorem C2_sum_check : (mainBlockLetters.map fun letters =>
    blockOutsideCount (transformed10Atom letters.1) (transformed5Atom letters.2)).sum =
    12839823 := by
  native_decide

end ShannonBounds.C7Improvement
