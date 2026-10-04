import C7Improvement.HigherGadgets

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 16000

def p5 : Profile6 := ⟨367,8,367,322,26,19⟩
def p10 := p5.gao p5
def p10A := p5.flip.gao p5
def p10D := p5.gao p5.flip
def p15X := p10.gao p5
def p15AX := p10A.gao p5
def p15DX := p10D.gao p5.flip
def p15het : Profile6 := ⟨49495055,2504616,49433743,35275258,6703815,7454670⟩
def p15Ahet : Profile6 := ⟨49495055,2504616,49432527,35303606,5948463,8180458⟩
def p15Afull : Profile6 := ⟨49495055,2504616,49433743,35275258,5978027,8180458⟩
def p30 := p15X.heterogeneous p15het p15het 49495055 49495055 12839823 12839823
def p25 := p15AX.heterogeneous p10D p15Ahet 49495055 49495055 12839823 12839823
def p25Rbefore := p15AX.heterogeneous p10D p15Ahet 49495055 49433743 12839823 14045805
def p25R := p25Rbefore.flip
def p40n8 := p15DX.heterogeneous p25 p15Ahet.flip 49433743 49495055 14045805 12839823
def pL30 := p15AX.gao p15Ahet.flip
def pOld30 := p15AX.heterogeneous p15Ahet.flip p15Ahet 49495055 49430863 12839823 14088465
def pNew30 := p15AX.heterogeneous p15Ahet.flip p15Afull 49495055 49495055 12839823 12839823
def p55 := pL30.heterogeneous p25R pOld30 2455726444728097 2455726444728097 841760069965664 841760069965664
def pFlip55 := p55.flip
def pNew40 := pL30.heterogeneous p10D pNew30 2455726444728097 2455726444728097 841760069965664 841760069965664

attribute [local irreducible] BaseC7.base G10 G10A G10D G15X G15AX G15DX G15het G15Ahet G15Afull
attribute [local irreducible] G30n6 G25n8 G25Rbeforeflip G25R G40n8 L30 oldL30sibling new_L30_sibling G55 flipG55 new_G40 J15 J30

theorem hp5 : HasProfile BaseC7.base p5 :=
  ⟨BaseC7.base_N, BaseC7.base_d, BaseC7.base_L, BaseC7.base_eta,
    BaseC7.base_Xc_true, BaseC7.base_Xc_false⟩

theorem hp10 : HasProfile G10 p10 := by
  rw [G10]
  exact hp5.gao hp5

theorem hp10A : HasProfile G10A p10A := by
  rw [G10A]
  exact hp5.flip.gao hp5

theorem hp10D : HasProfile G10D p10D := by
  rw [G10D]
  exact hp5.gao hp5.flip

theorem hp15X : HasProfile G15X p15X := by
  rw [G15X]
  exact hp10.gao hp5

theorem hp15AX : HasProfile G15AX p15AX := by
  rw [G15AX]
  exact hp10A.gao hp5

theorem hp15DX : HasProfile G15DX p15DX := by
  rw [G15DX]
  exact hp10D.gao hp5.flip

theorem hp15het : HasProfile G15het p15het := HasProfile.of_tuple G15het_profile
theorem hp15Ahet : HasProfile G15Ahet p15Ahet := HasProfile.of_tuple G15Ahet_profile
theorem hp15Afull : HasProfile G15Afull p15Afull := HasProfile.of_tuple G15Afull_profile

theorem J15_card_num : J15.card = 49495055 := by
  rw [J15_card, hp15X.main]
  rfl

theorem hp30 : HasProfile G30n6 p30 := by
  rw [G30n6]
  exact hp15X.heterogeneous hp15het hp15het G15het_sibling.2.1.symm G15het_sibling.2.2.1.symm
    J15 J15 J15_independent J15_independent 49495055 49495055 12839823 12839823
    J15_card_num J15_card_num C2_outside_G15X C2_outside_G15X

theorem hp25 : HasProfile G25n8 p25 := by
  rw [G25n8]
  exact hp15AX.heterogeneous hp10D hp15Ahet G15Ahet_sibling.1.symm G15Ahet_sibling.2.symm
    J15 J15 J15_independent J15_independent 49495055 49495055 12839823 12839823
    J15_card_num J15_card_num C2_outside_G15AX C2_outside_G15AX

theorem hp25Rbefore : HasProfile G25Rbeforeflip p25Rbefore := by
  rw [G25Rbeforeflip]
  exact hp15AX.heterogeneous hp10D hp15Ahet G15Ahet_sibling.1.symm G15Ahet_sibling.2.symm
    J15 G15het.X J15_independent G15het.hX 49495055 49433743 12839823 14045805
    J15_card_num hp15het.auxiliary C2_outside_G15AX C3_outside_G15AX

theorem hp25R : HasProfile G25R p25R := by
  rw [G25R]
  exact hp25Rbefore.flip

theorem hp40n8 : HasProfile G40n8 p40n8 := by
  rw [G40n8]
  exact hp15DX.heterogeneous hp25 hp15Ahet.flip G15DX_flipG15Ahet_ports G15DX_flipG15Ahet_ep
    G15het.X J15 G15het.hX J15_independent 49433743 49495055 14045805 12839823
    hp15het.auxiliary J15_card_num C3_outside_G15DX C2_outside_G15DX

theorem hpL30 : HasProfile L30 pL30 := by
  rw [L30]
  exact hp15AX.gao hp15Ahet.flip

theorem G15AX_auxiliary_card : G15AX.X.card = 49430863 := hp15AX.auxiliary

theorem G15AX_own_outside : (outside G15AX G15AX.X).card = 14088465 := by
  rw [own_outside_card, hp15AX.auxiliary, hp15AX.neutral]
  rfl

theorem hpOld30 : HasProfile oldL30sibling pOld30 := by
  rw [oldL30sibling]
  exact hp15AX.heterogeneous hp15Ahet.flip hp15Ahet G15Ahet_sibling.1.symm G15Ahet_sibling.2.symm
    J15 G15AX.X J15_independent G15AX.hX 49495055 49430863 12839823 14088465
    J15_card_num G15AX_auxiliary_card C2_outside_G15AX G15AX_own_outside

theorem hpNew30 : HasProfile new_L30_sibling pNew30 := by
  rw [new_L30_sibling]
  exact hp15AX.heterogeneous hp15Ahet.flip hp15Afull G15Afull_sibling.1.symm G15Afull_sibling.2.symm
    J15 J15 J15_independent J15_independent 49495055 49495055 12839823 12839823
    J15_card_num J15_card_num C2_outside_G15AX C2_outside_G15AX

theorem hp55 : HasProfile G55 p55 := by
  rw [G55]
  exact hpL30.heterogeneous hp25R hpOld30 oldL30sibling_ports.symm oldL30sibling_ep.symm
    J30 J30 J30_independent J30_independent 2455726444728097 2455726444728097 841760069965664 841760069965664
    J30_card J30_card C4_outside_L30 C4_outside_L30

theorem hpFlip55 : HasProfile flipG55 pFlip55 := by
  rw [flipG55]
  exact hp55.flip

theorem hpNew40 : HasProfile new_G40 pNew40 := by
  rw [new_G40]
  exact hpL30.heterogeneous hp10D hpNew30 new_L30_sibling_ports.symm new_L30_sibling_ep.symm
    J30 J30 J30_independent J30_independent 2455726444728097 2455726444728097 841760069965664 841760069965664
    J30_card J30_card C4_outside_L30 C4_outside_L30

def Profile6.weights (profile : Profile6) : Letter → ℕ
  | .B => profile.main - profile.ports | .N => profile.neutral
  | .A => profile.vertical | .D => profile.horizontal
  | .O | .H | .V => profile.ports

theorem HasProfile.weights {Point : Type*} [Fintype Point] [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] {system : RichPortSystem graph} {profile : Profile6}
    (correct : HasProfile system profile) (letter : Letter) :
    system.toRealisation.w letter = profile.weights letter := by
  rw [w_toRealisation]
  cases letter
  · rw [card_fam_B, correct.main, correct.ports]
    rfl
  · exact correct.neutral
  · exact correct.vertical
  · exact correct.horizontal
  · exact correct.ports
  · rw [card_fam_H]
    exact correct.ports
  · rw [card_fam_V]
    exact correct.ports

end ShannonBounds.C7Improvement
