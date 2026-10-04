import C7Improvement.Profile

namespace ShannonBounds.C7Improvement

open RichPortSystem

variable {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]
variable (left : RichPortSystem GL) (right : RichPortSystem GR)
variable (neutralSide hSide vSide : Finset Left)
variable (neutralIndependent : GL.IsIndepSet ↑neutralSide)
variable (hIndependent : GL.IsIndepSet ↑hSide) (vIndependent : GL.IsIndepSet ↑vSide)
variable (neutralSeparated : ∀ point ∈ neutralSide,
  ¬ (footprint left false point ∧ footprint left true point))

theorem heterogeneousGao_N :
    (heterogeneousGao left right neutralSide hSide vSide
      neutralIndependent hIndependent vIndependent neutralSeparated).N = (gao left right).N := rfl

theorem heterogeneousGao_d :
    (heterogeneousGao left right neutralSide hSide vSide
      neutralIndependent hIndependent vIndependent neutralSeparated).d = (gao left right).d := rfl

theorem heterogeneousGao_L :
    (heterogeneousGao left right neutralSide hSide vSide
      neutralIndependent hIndependent vIndependent neutralSeparated).L =
      neutralSide.card * right.eta + hSide.card * (right.Xc true).card +
        vSide.card * (right.Xc false).card := by
  change (heterogeneousAux (flip right) neutralSide hSide vSide).card = _
  rw [card_heterogeneousAux, flip_Xstar, flip_Xc, flip_Xc]
  rfl

theorem heterogeneousGao_eta :
    (heterogeneousGao left right neutralSide hSide vSide
      neutralIndependent hIndependent vIndependent neutralSeparated).eta =
      (auxiliaryNeutral left neutralSide).card * right.eta +
        (outside left hSide).card * (right.Xc true).card +
        (outside left vSide).card * (right.Xc false).card := by
  change (heterogeneousLift left (flip right) neutralSide hSide vSide
    neutralIndependent hIndependent vIndependent neutralSeparated).Xstar.card = _
  rw [card_heterogeneousLift_Xstar, flip_Xstar, flip_Xc, flip_Xc]
  rfl

theorem heterogeneousGao_h :
    ((heterogeneousGao left right neutralSide hSide vSide
      neutralIndependent hIndependent vIndependent neutralSeparated).Xc true).card =
      (auxiliaryFoot left neutralSide true).card * right.eta +
        (vSide.card - (outside left vSide).card) * (right.Xc false).card := by
  change ((heterogeneousLift left (flip right) neutralSide hSide vSide
    neutralIndependent hIndependent vIndependent neutralSeparated).Xc true).card = _
  rw [card_heterogeneousLift_Xc, flip_Xstar, flip_Xc]
  rfl

theorem heterogeneousGao_v :
    ((heterogeneousGao left right neutralSide hSide vSide
      neutralIndependent hIndependent vIndependent neutralSeparated).Xc false).card =
      (auxiliaryFoot left neutralSide false).card * right.eta +
        (hSide.card - (outside left hSide).card) * (right.Xc true).card := by
  change ((heterogeneousLift left (flip right) neutralSide hSide vSide
    neutralIndependent hIndependent vIndependent neutralSeparated).Xc false).card = _
  rw [card_heterogeneousLift_Xc, flip_Xstar, flip_Xc]
  rfl

end ShannonBounds.C7Improvement
