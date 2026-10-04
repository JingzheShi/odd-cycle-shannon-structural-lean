import C7Improvement.CountC4

namespace ShannonBounds.C7Improvement

open RichPortSystem

structure Profile6 where
  main : ℕ
  ports : ℕ
  auxiliary : ℕ
  neutral : ℕ
  horizontal : ℕ
  vertical : ℕ
  deriving DecidableEq

structure HasProfile {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (system : RichPortSystem graph) (profile : Profile6) : Prop where
  main : system.N = profile.main
  ports : system.d = profile.ports
  auxiliary : system.L = profile.auxiliary
  neutral : system.eta = profile.neutral
  horizontal : (system.Xc true).card = profile.horizontal
  vertical : (system.Xc false).card = profile.vertical

def Profile6.flip (profile : Profile6) : Profile6 :=
  ⟨profile.main, profile.ports, profile.auxiliary, profile.neutral, profile.vertical, profile.horizontal⟩

def Profile6.gao (left right : Profile6) : Profile6 where
  main := (left.main - left.ports) * (right.main - right.ports) +
    left.auxiliary * right.ports + left.ports * right.auxiliary
  ports := left.neutral * right.ports + left.ports * right.neutral
  auxiliary := left.auxiliary * right.auxiliary
  neutral := left.neutral * right.neutral +
    (left.auxiliary - left.neutral) * (right.auxiliary - right.neutral)
  horizontal := left.neutral * right.vertical + left.horizontal * right.neutral
  vertical := left.neutral * right.horizontal + left.vertical * right.neutral

def Profile6.heterogeneous (left right sibling : Profile6)
    (hSize vSize hOutside vOutside : ℕ) : Profile6 where
  main := (left.gao right).main
  ports := (left.gao right).ports
  auxiliary := sibling.auxiliary * right.neutral + hSize * right.horizontal + vSize * right.vertical
  neutral := sibling.neutral * right.neutral + hOutside * right.horizontal + vOutside * right.vertical
  horizontal := sibling.horizontal * right.neutral + (vSize - vOutside) * right.vertical
  vertical := sibling.vertical * right.neutral + (hSize - hOutside) * right.horizontal

theorem HasProfile.of_tuple {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] {system : RichPortSystem graph} {profile : Profile6}
    (tuple : system.N = profile.main ∧ system.d = profile.ports ∧
      system.L = profile.auxiliary ∧ system.eta = profile.neutral ∧
      (system.Xc true).card = profile.horizontal ∧ (system.Xc false).card = profile.vertical) :
    HasProfile system profile :=
  ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2.1, tuple.2.2.2.2.2⟩

theorem HasProfile.flip {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] {system : RichPortSystem graph} {profile : Profile6}
    (correct : HasProfile system profile) : HasProfile (flip system) profile.flip := by
  refine ⟨correct.main, correct.ports, correct.auxiliary, ?_, ?_, ?_⟩
  · rw [flip_eta]
    exact correct.neutral
  · rw [flip_Xc]
    exact correct.vertical
  · rw [flip_Xc]
    exact correct.horizontal

theorem card_gao_Xc {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
    {GL : SimpleGraph Left} {GR : SimpleGraph Right}
    [DecidableRel GL.Adj] [DecidableRel GR.Adj]
    (left : RichPortSystem GL) (right : RichPortSystem GR) (direction : Bool) :
    ((gao left right).Xc direction).card =
      left.eta * (right.Xc (!direction)).card + (left.Xc direction).card * right.eta := by
  rw [gao_Xc, Finset.card_union_of_disjoint
    (Finset.disjoint_product.mpr (Or.inl (neutral_disjoint_class left direction))),
    Finset.card_product, Finset.card_product]
  rfl

theorem HasProfile.gao {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
    {GL : SimpleGraph Left} {GR : SimpleGraph Right}
    [DecidableRel GL.Adj] [DecidableRel GR.Adj]
    {left : RichPortSystem GL} {right : RichPortSystem GR} {lp rp : Profile6}
    (leftCorrect : HasProfile left lp) (rightCorrect : HasProfile right rp) :
    HasProfile (gao left right) (lp.gao rp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gao_N, leftCorrect.main, leftCorrect.ports, leftCorrect.auxiliary,
      rightCorrect.main, rightCorrect.ports, rightCorrect.auxiliary]
    rfl
  · rw [gao_d, leftCorrect.neutral, leftCorrect.ports, rightCorrect.neutral, rightCorrect.ports]
    rfl
  · rw [gao_L, leftCorrect.auxiliary, rightCorrect.auxiliary]
    rfl
  · rw [gao_eta, leftCorrect.neutral, leftCorrect.auxiliary,
      rightCorrect.neutral, rightCorrect.auxiliary]
    rfl
  · rw [card_gao_Xc, Bool.not_true, leftCorrect.neutral, rightCorrect.vertical,
      leftCorrect.horizontal, rightCorrect.neutral]
    rfl
  · rw [card_gao_Xc, Bool.not_false, leftCorrect.neutral, rightCorrect.horizontal,
      leftCorrect.vertical, rightCorrect.neutral]
    rfl

theorem HasProfile.heterogeneous {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
    {GL : SimpleGraph Left} {GR : SimpleGraph Right}
    [DecidableRel GL.Adj] [DecidableRel GR.Adj]
    {left sibling : RichPortSystem GL} {right : RichPortSystem GR} {lp sp rp : Profile6}
    (leftCorrect : HasProfile left lp) (rightCorrect : HasProfile right rp)
    (siblingCorrect : HasProfile sibling sp)
    (samePorts : left.ports = sibling.ports) (sameEndpoints : left.ep = sibling.ep)
    (hSide vSide : Finset Left) (hIndependent : GL.IsIndepSet ↑hSide) (vIndependent : GL.IsIndepSet ↑vSide)
    (hSize vSize hOutside vOutside : ℕ)
    (hCard : hSide.card = hSize) (vCard : vSide.card = vSize)
    (hCount : (outside left hSide).card = hOutside) (vCount : (outside left vSide).card = vOutside) :
    HasProfile (heterogeneousGao left right sibling.X hSide vSide sibling.hX hIndependent vIndependent
      (sibling_admissible left sibling samePorts sameEndpoints))
      (lp.heterogeneous rp sp hSize vSize hOutside vOutside) := by
  have siblingAuxiliary : sibling.X.card = sp.auxiliary := siblingCorrect.auxiliary
  have siblingNeutral : sibling.Xstar.card = sp.neutral := siblingCorrect.neutral
  have ordinary := leftCorrect.gao rightCorrect
  refine ⟨ordinary.main, ordinary.ports, ?_, ?_, ?_, ?_⟩
  · rw [heterogeneousGao_L, siblingAuxiliary, rightCorrect.neutral, hCard, vCard,
      rightCorrect.horizontal, rightCorrect.vertical]
    rfl
  · rw [heterogeneousGao_eta, sibling_auxiliaryNeutral left sibling samePorts sameEndpoints,
      siblingNeutral, rightCorrect.neutral, hCount, vCount, rightCorrect.horizontal, rightCorrect.vertical]
    rfl
  · rw [heterogeneousGao_h, sibling_auxiliaryFoot left sibling samePorts sameEndpoints true,
      siblingCorrect.horizontal, rightCorrect.neutral, vCard, vCount, rightCorrect.vertical]
    rfl
  · rw [heterogeneousGao_v, sibling_auxiliaryFoot left sibling samePorts sameEndpoints false,
      siblingCorrect.vertical, rightCorrect.neutral, hCard, hCount, rightCorrect.horizontal]
    rfl

end ShannonBounds.C7Improvement
