import C7Improvement.Heterogeneous

namespace ShannonBounds.C7Improvement

open RichPortSystem

variable {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]

theorem neutral_disjoint_class (system : RichPortSystem GR) (direction : Bool) :
    Disjoint system.Xstar (system.Xc direction) := by
  rw [Finset.disjoint_left]
  intro point neutral classMember
  cases direction
  · exact (system.mem_Xstar.mp neutral).2.1 classMember
  · exact (system.mem_Xstar.mp neutral).2.2 classMember

theorem card_heterogeneousAux (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left) :
    (heterogeneousAux right neutralSide falseSide trueSide).card =
      neutralSide.card * right.Xstar.card + falseSide.card * (right.Xc false).card +
      trueSide.card * (right.Xc true).card := by
  have neutralFalse : Disjoint (neutralSide ×ˢ right.Xstar) (falseSide ×ˢ right.Xc false) :=
    Finset.disjoint_product.mpr (Or.inr (neutral_disjoint_class right false))
  have neutralTrue : Disjoint (neutralSide ×ˢ right.Xstar) (trueSide ×ˢ right.Xc true) :=
    Finset.disjoint_product.mpr (Or.inr (neutral_disjoint_class right true))
  have falseTrue : Disjoint (falseSide ×ˢ right.Xc false) (trueSide ×ˢ right.Xc true) :=
    Finset.disjoint_product.mpr (Or.inr right.Xc_disjoint)
  rw [heterogeneousAux,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨neutralTrue, falseTrue⟩),
    Finset.card_union_of_disjoint neutralFalse,
    Finset.card_product, Finset.card_product, Finset.card_product]

theorem inside_card (left : RichPortSystem GL) (side : Finset Left) :
    (inside left side).card = side.card - (outside left side).card := by
  have total : (inside left side).card + (outside left side).card = side.card :=
    Finset.card_filter_add_card_filter_not (s := side) (near GL left.Xstar)
  omega

theorem card_heterogeneousLift_Xc (left : RichPortSystem GL) (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left)
    (neutralIndependent : GL.IsIndepSet ↑neutralSide)
    (falseIndependent : GL.IsIndepSet ↑falseSide)
    (trueIndependent : GL.IsIndepSet ↑trueSide)
    (neutralSeparated : ∀ point ∈ neutralSide,
      ¬ (footprint left false point ∧ footprint left true point)) (direction : Bool) :
    ((heterogeneousLift left right neutralSide falseSide trueSide
      neutralIndependent falseIndependent trueIndependent neutralSeparated).Xc direction).card =
      (auxiliaryFoot left neutralSide direction).card * right.Xstar.card +
      ((if direction then trueSide else falseSide).card -
        (outside left (if direction then trueSide else falseSide)).card) *
        (right.Xc direction).card := by
  rw [heterogeneousLift_Xc]
  rw [Finset.card_union_of_disjoint
    (Finset.disjoint_product.mpr (Or.inr (neutral_disjoint_class right direction))),
    Finset.card_product, Finset.card_product, inside_card]

theorem card_heterogeneousLift_Xstar (left : RichPortSystem GL) (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left)
    (neutralIndependent : GL.IsIndepSet ↑neutralSide)
    (falseIndependent : GL.IsIndepSet ↑falseSide)
    (trueIndependent : GL.IsIndepSet ↑trueSide)
    (neutralSeparated : ∀ point ∈ neutralSide,
      ¬ (footprint left false point ∧ footprint left true point)) :
    (heterogeneousLift left right neutralSide falseSide trueSide
      neutralIndependent falseIndependent trueIndependent neutralSeparated).Xstar.card =
      (auxiliaryNeutral left neutralSide).card * right.Xstar.card +
      (outside left falseSide).card * (right.Xc false).card +
      (outside left trueSide).card * (right.Xc true).card := by
  rw [heterogeneousLift_Xstar]
  exact card_heterogeneousAux right (auxiliaryNeutral left neutralSide)
    (outside left falseSide) (outside left trueSide)

end ShannonBounds.C7Improvement
