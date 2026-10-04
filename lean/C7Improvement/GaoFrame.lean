import C7Improvement.ProfileArithmetic

namespace ShannonBounds.C7Improvement

variable {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]

theorem heterogeneousGao_sibling (left : RichPortSystem GL) (right : RichPortSystem GR)
    (neutralSide hSide vSide : Finset Left)
    (neutralIndependent : GL.IsIndepSet ↑neutralSide)
    (hIndependent : GL.IsIndepSet ↑hSide) (vIndependent : GL.IsIndepSet ↑vSide)
    (neutralSeparated : ∀ point ∈ neutralSide,
      ¬ (footprint left false point ∧ footprint left true point)) :
    let result := heterogeneousGao left right neutralSide hSide vSide
      neutralIndependent hIndependent vIndependent neutralSeparated
    result.I = (gao left right).I ∧ result.ports = (gao left right).ports ∧
      result.ep = (gao left right).ep ∧ result.side = (gao left right).side :=
  heterogeneousLift_sibling left (flip right) neutralSide hSide vSide
    neutralIndependent hIndependent vIndependent neutralSeparated

end ShannonBounds.C7Improvement
