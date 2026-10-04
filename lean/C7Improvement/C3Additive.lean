import C7Improvement.C3Geometry

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 G15het Jplus

theorem C3_filter_card (accepted : (BaseC7.Code × BaseC7.Code) × BaseC7.Code → Prop)
    [DecidablePred accepted] :
    (G15het.X.filter accepted).card =
      ((G10.X ×ˢ BaseC7.base.Xstar).filter accepted).card +
      ((Jplus ×ˢ BaseC7.base.Xc true).filter accepted).card +
      ((Jplus ×ˢ BaseC7.base.Xc false).filter accepted).card := by
  have disjoint01 : Disjoint ((G10.X ×ˢ BaseC7.base.Xstar).filter accepted)
      ((Jplus ×ˢ BaseC7.base.Xc true).filter accepted) :=
    C3_raw_disjoint01.mono
      (Finset.filter_subset accepted (G10.X ×ˢ BaseC7.base.Xstar))
      (Finset.filter_subset accepted (Jplus ×ˢ BaseC7.base.Xc true))
  have disjoint02 : Disjoint ((G10.X ×ˢ BaseC7.base.Xstar).filter accepted)
      ((Jplus ×ˢ BaseC7.base.Xc false).filter accepted) :=
    C3_raw_disjoint02.mono
      (Finset.filter_subset accepted (G10.X ×ˢ BaseC7.base.Xstar))
      (Finset.filter_subset accepted (Jplus ×ˢ BaseC7.base.Xc false))
  have disjoint12 : Disjoint ((Jplus ×ˢ BaseC7.base.Xc true).filter accepted)
      ((Jplus ×ˢ BaseC7.base.Xc false).filter accepted) :=
    C3_raw_disjoint12.mono
      (Finset.filter_subset accepted (Jplus ×ˢ BaseC7.base.Xc true))
      (Finset.filter_subset accepted (Jplus ×ˢ BaseC7.base.Xc false))
  rw [G15het_X, Finset.filter_union, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨disjoint02, disjoint12⟩),
    Finset.card_union_of_disjoint disjoint01]

end ShannonBounds.C7Improvement
