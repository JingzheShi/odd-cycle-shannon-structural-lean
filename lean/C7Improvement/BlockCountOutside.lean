import C7Improvement.BlockCount15
import C7Improvement.Outside15

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 100000
set_option maxHeartbeats 100000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 G15X
attribute [local irreducible] blockOutsideCount baseAtom

theorem blockOutsideCount_outside (points : List (BaseC7.Code × BaseC7.Code))
    (unique : points.Nodup) (letter : Letter) :
    ((points.toFinset ×ˢ BaseC7.base.fam letter).filter outside15).card =
      blockOutsideCount points (baseAtom letter) := by
  exact blockOutsideCount_spec points unique letter

theorem blockOutsideCount_set (points : List (BaseC7.Code × BaseC7.Code))
    (unique : points.Nodup) (actual : Finset (BaseC7.Code × BaseC7.Code))
    (equal : points.toFinset = actual) (letter : Letter) :
    ((actual ×ˢ BaseC7.base.fam letter).filter outside15).card =
      blockOutsideCount points (baseAtom letter) := by
  rw [← equal]
  exact blockOutsideCount_outside points unique letter

end ShannonBounds.C7Improvement
