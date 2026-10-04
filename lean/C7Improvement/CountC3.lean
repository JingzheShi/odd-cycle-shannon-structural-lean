import C7Improvement.C3Data
import C7Improvement.G15Oriented
import C7Improvement.SparseCount
import C7Improvement.BaseXBridge
import C7Improvement.Atoms10
import C7Improvement.Flags15
import C7Improvement.BlockCount15
import C7Improvement.C3Geometry
import C7Improvement.C3Additive
import C7Improvement.Outside15
import C7Improvement.BlockCountOutside
import C7Improvement.C3Neutral
import C7Improvement.C3Sum

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem
open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 100000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 G15X G15het Jplus JplusList X10List
attribute [local irreducible] neutralNear restNear inNeutral10 inRest10
attribute [local irreducible] blockOutsideCount weight10 weight5 baseAtom

theorem C3_count : (G15het.X.filter outside15).card = 14045805 := by
  exact (C3_filter_card outside15).trans
    C3_sum_count

end ShannonBounds.C7Improvement
