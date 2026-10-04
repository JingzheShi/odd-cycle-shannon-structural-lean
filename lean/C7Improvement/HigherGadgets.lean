import C7Improvement.GaoFrame

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 10000
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 16000

attribute [local irreducible] BaseC7.base G10 G10D G15X G15AX G15Ahet G15Afull G15het
attribute [local irreducible] J15 J30 L30 G25R

def oldL30sibling : RichPortSystem
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5)) :=
  heterogeneousGao G15AX (flip G15Ahet) G15Ahet.X J15 G15AX.X
    G15Ahet.hX J15_independent G15AX.hX
    (sibling_admissible G15AX G15Ahet G15Ahet_sibling.1.symm G15Ahet_sibling.2.symm)

theorem oldL30sibling_ports : oldL30sibling.ports = L30.ports := by
  rw [oldL30sibling, L30]
  exact (heterogeneousGao_sibling G15AX (flip G15Ahet) G15Ahet.X J15 G15AX.X _ _ _ _).2.1
theorem oldL30sibling_ep : oldL30sibling.ep = L30.ep := by
  rw [oldL30sibling, L30]
  exact (heterogeneousGao_sibling G15AX (flip G15Ahet) G15Ahet.X J15 G15AX.X _ _ _ _).2.2.1

def new_L30_sibling : RichPortSystem
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5)) :=
  heterogeneousGao G15AX (flip G15Ahet) G15Afull.X J15 J15
    G15Afull.hX J15_independent J15_independent
    (sibling_admissible G15AX G15Afull G15Afull_sibling.1.symm G15Afull_sibling.2.symm)

theorem new_L30_sibling_ports : new_L30_sibling.ports = L30.ports := by
  rw [new_L30_sibling, L30]
  exact (heterogeneousGao_sibling G15AX (flip G15Ahet) G15Afull.X J15 J15 _ _ _ _).2.1
theorem new_L30_sibling_ep : new_L30_sibling.ep = L30.ep := by
  rw [new_L30_sibling, L30]
  exact (heterogeneousGao_sibling G15AX (flip G15Ahet) G15Afull.X J15 J15 _ _ _ _).2.2.1

def G55 : RichPortSystem
    (strongProd
      (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5))
      (strongProd (strongProd (strongProd G5 G5) G5) (strongProd G5 G5))) :=
  heterogeneousGao L30 G25R oldL30sibling.X J30 J30
    oldL30sibling.hX J30_independent J30_independent
    (sibling_admissible L30 oldL30sibling oldL30sibling_ports.symm oldL30sibling_ep.symm)

def flipG55 := flip G55

def new_G40 : RichPortSystem
    (strongProd
      (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5))
      (strongProd G5 G5)) :=
  heterogeneousGao L30 G10D new_L30_sibling.X J30 J30
    new_L30_sibling.hX J30_independent J30_independent
    (sibling_admissible L30 new_L30_sibling new_L30_sibling_ports.symm new_L30_sibling_ep.symm)

theorem outside_reference_eq {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (first second : RichPortSystem graph)
    (equalNeutral : first.Xstar = second.Xstar) (side : Finset Point) :
    outside first side = outside second side := by
  simp only [outside, equalNeutral]

theorem C2_outside_G15X : (outside G15X J15).card = 12839823 := C2_count

theorem C2_outside_G15AX : (outside G15AX J15).card = 12839823 := by
  rw [outside_reference_eq G15AX G15X G15AX_neutral]
  exact C2_outside_G15X

theorem C2_outside_G15DX : (outside G15DX J15).card = 12839823 := by
  rw [outside_reference_eq G15DX G15X G15DX_neutral]
  exact C2_outside_G15X

theorem C3_outside_G15AX : (outside G15AX G15het.X).card = 14045805 := by
  rw [outside_reference_eq G15AX G15X G15AX_neutral]
  exact C3_count

theorem C3_outside_G15DX : (outside G15DX G15het.X).card = 14045805 := by
  rw [outside_reference_eq G15DX G15X G15DX_neutral]
  exact C3_count

theorem C4_outside_L30 : (outside L30 J30).card = 841760069965664 := C4_count

end ShannonBounds.C7Improvement
