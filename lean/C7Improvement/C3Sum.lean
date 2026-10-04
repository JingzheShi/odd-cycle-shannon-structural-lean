import C7Improvement.C3Neutral
import C7Improvement.C3Numeric

namespace ShannonBounds.C7Improvement

open BaseC7

set_option maxRecDepth 10000
set_option maxHeartbeats 100000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 G15X Jplus JplusList X10List
attribute [local irreducible] blockOutsideCount weight10 weight5 baseAtom

theorem sum_three_equal {first second third first' second' third' : ℕ}
    (firstEqual : first = first') (secondEqual : second = second')
    (thirdEqual : third = third') : first + second + third = first' + second' + third' := by
  rw [firstEqual, secondEqual, thirdEqual]

theorem C3_sum_count :
    ((G10.X ×ˢ BaseC7.base.Xstar).filter outside15).card +
      ((Jplus ×ˢ BaseC7.base.Xc true).filter outside15).card +
      ((Jplus ×ˢ BaseC7.base.Xc false).filter outside15).card = 14045805 := by
  exact (sum_three_equal C3_neutral_count' C3_horizontal_count C3_vertical_count).trans
    C3_sum_check

end ShannonBounds.C7Improvement
