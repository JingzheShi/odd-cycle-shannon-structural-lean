import C7Improvement.G15Oriented

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

variable {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]

theorem heterogeneousGao_auxiliary (left : RichPortSystem GL) (right : RichPortSystem GR)
    (neutralSide hSide vSide : Finset Left)
    (neutralIndependent : GL.IsIndepSet ↑neutralSide)
    (hIndependent : GL.IsIndepSet ↑hSide) (vIndependent : GL.IsIndepSet ↑vSide)
    (neutralSeparated : ∀ point ∈ neutralSide,
      ¬ (footprint left false point ∧ footprint left true point)) :
    (heterogeneousGao left right neutralSide hSide vSide
      neutralIndependent hIndependent vIndependent neutralSeparated).X =
      (neutralSide ×ˢ right.Xstar) ∪ (hSide ×ˢ right.Xc true) ∪ (vSide ×ˢ right.Xc false) := by
  change heterogeneousAux (flip right) neutralSide hSide vSide = _
  rw [heterogeneousAux, flip_Xstar, flip_Xc, flip_Xc]
  rfl

attribute [local irreducible] BaseC7.base G10 G15het Jplus

theorem G15het_X : G15het.X =
    (G10.X ×ˢ BaseC7.base.Xstar) ∪ (Jplus ×ˢ BaseC7.base.Xc true) ∪
      (Jplus ×ˢ BaseC7.base.Xc false) := by
  rw [G15het, heterogeneousGao_auxiliary]

theorem C3_raw_disjoint01 : Disjoint (G10.X ×ˢ BaseC7.base.Xstar) (Jplus ×ˢ BaseC7.base.Xc true) :=
  Finset.disjoint_product.mpr (Or.inr (neutral_disjoint_class BaseC7.base true))

theorem C3_raw_disjoint02 : Disjoint (G10.X ×ˢ BaseC7.base.Xstar) (Jplus ×ˢ BaseC7.base.Xc false) :=
  Finset.disjoint_product.mpr (Or.inr (neutral_disjoint_class BaseC7.base false))

theorem C3_raw_disjoint12 : Disjoint (Jplus ×ˢ BaseC7.base.Xc true) (Jplus ×ˢ BaseC7.base.Xc false) :=
  Finset.disjoint_product.mpr (Or.inr BaseC7.base.Xc_disjoint.symm)

end ShannonBounds.C7Improvement
