import C7Improvement.BlockCountOutside
import C7Improvement.Atoms10

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 10000
set_option maxHeartbeats 100000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 G15X Jplus JplusList X10List
attribute [local irreducible] blockOutsideCount weight10 weight5 C3value baseAtom

theorem C3_neutral_count : ((G10.X ×ˢ BaseC7.base.fam .N).filter outside15).card =
    blockOutsideCount X10List (baseAtom .N) := by
  exact blockOutsideCount_set X10List X10List_nodup G10.X X10List_eq .N

theorem C3_neutral_count' : ((G10.X ×ˢ BaseC7.base.Xstar).filter outside15).card =
    blockOutsideCount X10List (baseAtom .N) := by
  simpa only [RichPortSystem.fam] using C3_neutral_count

theorem C3_horizontal_count : ((Jplus ×ˢ BaseC7.base.Xc true).filter outside15).card =
    blockOutsideCount JplusList (baseAtom .D) := by
  simpa only [RichPortSystem.fam] using
    blockOutsideCount_set JplusList JplusList_nodup Jplus JplusList_eq .D

theorem C3_vertical_count : ((Jplus ×ˢ BaseC7.base.Xc false).filter outside15).card =
    blockOutsideCount JplusList (baseAtom .A) := by
  simpa only [RichPortSystem.fam] using
    blockOutsideCount_set JplusList JplusList_nodup Jplus JplusList_eq .A

end ShannonBounds.C7Improvement
