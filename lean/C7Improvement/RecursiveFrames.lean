import C7Improvement.CountC2
import C7Improvement.CountC3

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem flip_ports {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (system : RichPortSystem graph) : (flip system).ports = system.ports := rfl

theorem flip_ep {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (system : RichPortSystem graph) :
    (flip system).ep = fun direction point => system.ep (!direction) point := rfl

theorem gao_flip_ports {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
    {GL : SimpleGraph Left} {GR : SimpleGraph Right}
    [DecidableRel GL.Adj] [DecidableRel GR.Adj]
    (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao (flip left) right).ports = (gao left (flip right)).ports := by
  rw [gao_ports, gao_ports, flip_Xstar, flip_Xstar]
  rfl

theorem gao_flip_ep {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
    {GL : SimpleGraph Left} {GR : SimpleGraph Right}
    [DecidableRel GL.Adj] [DecidableRel GR.Adj]
    (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (flip (gao (flip left) right)).ep = (gao left (flip right)).ep := by
  funext direction point
  simp only [flip, gao, liftRPS, liftEp, Bool.not_not]

attribute [local irreducible] BaseC7.base G10 G10A G10D G15X G15AX G15DX
attribute [local irreducible] G15Ahet G15Afull G15het Jplus J15

theorem G15Ahet_profile : G15Ahet.N = 49495055 ∧ G15Ahet.d = 2504616 ∧
    G15Ahet.L = 49432527 ∧ G15Ahet.eta = 35303606 ∧
    (G15Ahet.Xc true).card = 5948463 ∧ (G15Ahet.Xc false).card = 8180458 := by
  obtain ⟨mainSize, portsSize, auxiliarySize, neutralSize, horizontalSize, verticalSize⟩ := G10A_profile
  have auxiliaryCard : G10A.X.card = 134689 := auxiliarySize
  have neutralCard : G10A.Xstar.card = 105709 := neutralSize
  have ownOutside : (outside G10A G10A.X).card = 28980 := by
    rw [own_outside_card, auxiliarySize, neutralSize]
  have improvedOutside : (outside G10A Jplus).card = 27488 := by
    simpa only [outside, G10A_neutral] using C1_count
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [G15Ahet, heterogeneousGao_N, gao_N, mainSize, portsSize, auxiliarySize,
      BaseC7.base_N, BaseC7.base_d, BaseC7.base_L]
  · rw [G15Ahet, heterogeneousGao_d, gao_d, neutralSize, portsSize,
      BaseC7.base_eta, BaseC7.base_d]
  · rw [G15Ahet, heterogeneousGao_L, auxiliaryCard, BaseC7.base_eta, Jplus_card,
      BaseC7.base_Xc_true, BaseC7.base_Xc_false]
  · rw [G15Ahet, heterogeneousGao_eta, sibling_auxiliaryNeutral G10A G10A rfl rfl,
      neutralCard, BaseC7.base_eta, improvedOutside, ownOutside,
      BaseC7.base_Xc_true, BaseC7.base_Xc_false]
  · rw [G15Ahet, heterogeneousGao_h, sibling_auxiliaryFoot G10A G10A rfl rfl true,
      horizontalSize, BaseC7.base_eta, auxiliaryCard, ownOutside, BaseC7.base_Xc_false]
  · rw [G15Ahet, heterogeneousGao_v, sibling_auxiliaryFoot G10A G10A rfl rfl false,
      verticalSize, BaseC7.base_eta, Jplus_card, improvedOutside, BaseC7.base_Xc_true]

theorem G10D_flipG10A_ports : G10D.ports = (flip G10A).ports := by
  rw [G10D, G10A, flip_ports]
  exact (gao_flip_ports BaseC7.base BaseC7.base).symm

theorem G10D_flipG10A_ep : G10D.ep = (flip G10A).ep := by
  rw [G10D, G10A]
  exact (gao_flip_ep BaseC7.base BaseC7.base).symm

theorem G15DX_flipG15Ahet_ports : G15DX.ports = (flip G15Ahet).ports := by
  rw [flip_ports, G15Ahet_sibling.1, G15DX, G15AX, gao_ports, gao_ports,
    G10D_neutral, G10A_neutral, G10D_flipG10A_ports, flip_Xstar]
  rfl

theorem G15DX_flipG15Ahet_ep : G15DX.ep = (flip G15Ahet).ep := by
  rw [flip_ep, G15Ahet_sibling.2]
  funext direction point
  rw [G15DX, G15AX]
  change liftEp G10D (flip (flip BaseC7.base)) direction point =
    liftEp G10A (flip BaseC7.base) (!direction) point
  rw [liftEp, liftEp, G10D_flipG10A_ports, G10D_flipG10A_ep]
  rfl

def G30n6 : RichPortSystem
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5)) :=
  heterogeneousGao G15X G15het G15het.X J15 J15
    G15het.hX J15_independent J15_independent
    (sibling_admissible G15X G15het G15het_sibling.2.1.symm G15het_sibling.2.2.1.symm)

def G25n8 : RichPortSystem
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd G5 G5)) :=
  heterogeneousGao G15AX G10D G15Ahet.X J15 J15
    G15Ahet.hX J15_independent J15_independent
    (sibling_admissible G15AX G15Ahet G15Ahet_sibling.1.symm G15Ahet_sibling.2.symm)

def G25Rbeforeflip : RichPortSystem
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd G5 G5)) :=
  heterogeneousGao G15AX G10D G15Ahet.X J15 G15het.X
    G15Ahet.hX J15_independent G15het.hX
    (sibling_admissible G15AX G15Ahet G15Ahet_sibling.1.symm G15Ahet_sibling.2.symm)

def G25R := flip G25Rbeforeflip

def G40n8 : RichPortSystem
    (strongProd (strongProd (strongProd G5 G5) G5)
      (strongProd (strongProd (strongProd G5 G5) G5) (strongProd G5 G5))) :=
  heterogeneousGao G15DX G25n8 (flip G15Ahet).X G15het.X J15
    (flip G15Ahet).hX G15het.hX J15_independent
    (sibling_admissible G15DX (flip G15Ahet) G15DX_flipG15Ahet_ports G15DX_flipG15Ahet_ep)

def L30 : RichPortSystem
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5)) :=
  gao G15AX (flip G15Ahet)

def sourceJ30 := gao G15het G15het

end ShannonBounds.C7Improvement
