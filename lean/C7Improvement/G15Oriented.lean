import C7Improvement.G15

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem flip_N {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (system : RichPortSystem graph) : (flip system).N = system.N := rfl

theorem flip_d {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (system : RichPortSystem graph) : (flip system).d = system.d := rfl

theorem flip_L {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (system : RichPortSystem graph) : (flip system).L = system.L := rfl

theorem flip_eta {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (system : RichPortSystem graph) : (flip system).eta = system.eta := by
  exact congrArg Finset.card (flip_Xstar system)

theorem own_outside {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (system : RichPortSystem graph) :
    outside system system.X = system.X \ system.Xstar := by
  ext point
  simp only [outside, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨member, noNearby⟩
    exact ⟨member, fun neutral => noNearby ((near_neutral_iff system member).mpr neutral)⟩
  · rintro ⟨member, notNeutral⟩
    exact ⟨member, fun nearby => notNeutral ((near_neutral_iff system member).mp nearby)⟩

theorem own_outside_card {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (system : RichPortSystem graph) :
    (outside system system.X).card = system.L - system.eta := by
  rw [own_outside, Finset.card_sdiff_of_subset system.Xstar_subset_X]
  rfl

theorem G10A_X : G10A.X = G10.X := rfl

theorem G10D_X : G10D.X = G10.X := rfl

attribute [local irreducible] BaseC7.base G10 G10A G10D Jplus

theorem G10A_profile : G10A.N = 134753 ∧ G10A.d = 5152 ∧ G10A.L = 134689 ∧
    G10A.eta = 105709 ∧ (G10A.Xc true).card = 12236 ∧ (G10A.Xc false).card = 16744 := by
  have baseNeutral : BaseC7.base.Xstar.card = 322 := BaseC7.base_eta
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [G10A, gao_N, flip_N, flip_d, flip_L, BaseC7.base_N, BaseC7.base_d, BaseC7.base_L]
  · rw [G10A, gao_d, flip_eta, flip_d, BaseC7.base_eta, BaseC7.base_d]
  · rw [G10A, gao_L, flip_L, BaseC7.base_L]
  · rw [G10A, gao_eta, flip_L, flip_eta, BaseC7.base_eta, BaseC7.base_L]
  · rw [G10A, gao, card_liftRPS_Xc]
    simp only [flip_Xstar, flip_Xc, Bool.not_true]
    rw [baseNeutral, BaseC7.base_Xc_false]
  · rw [G10A, gao, card_liftRPS_Xc]
    simp only [flip_Xstar, flip_Xc, Bool.not_false]
    rw [baseNeutral, BaseC7.base_Xc_true]

theorem G15AX_neutral : G15AX.Xstar = G15X.Xstar := by
  rw [G15AX, G15X, gao_Xstar, gao_Xstar, G10A_neutral, G10A_X]

theorem G15DX_neutral : G15DX.Xstar = G15X.Xstar := by
  rw [G15DX, G15X, gao_Xstar, gao_Xstar, G10D_neutral, G10D_X, flip_Xstar]
  rfl

def G15Ahet : RichPortSystem (strongProd (strongProd G5 G5) G5) :=
  heterogeneousGao G10A BaseC7.base G10A.X Jplus G10A.X
    G10A.hX Jplus_independent G10A.hX G10A.hsep

def G15Afull : RichPortSystem (strongProd (strongProd G5 G5) G5) :=
  heterogeneousGao G10A BaseC7.base G10A.X Jplus Jplus
    G10A.hX Jplus_independent Jplus_independent G10A.hsep

theorem G15Ahet_sibling : G15Ahet.ports = G15AX.ports ∧ G15Ahet.ep = G15AX.ep := ⟨rfl, rfl⟩

theorem G15Afull_sibling : G15Afull.ports = G15AX.ports ∧ G15Afull.ep = G15AX.ep := ⟨rfl, rfl⟩

theorem G15Afull_profile : G15Afull.N = 49495055 ∧ G15Afull.d = 2504616 ∧
    G15Afull.L = 49433743 ∧ G15Afull.eta = 35275258 ∧
    (G15Afull.Xc true).card = 5978027 ∧ (G15Afull.Xc false).card = 8180458 := by
  obtain ⟨main10, ports10, auxiliary10, neutral10, h10, v10⟩ := G10A_profile
  have neutral10Card : G10A.Xstar.card = 105709 := neutral10
  have auxiliary10Card : G10A.X.card = 134689 := auxiliary10
  have outsideCount : (outside G10A Jplus).card = 27488 := by
    simpa only [outside, G10A_neutral] using C1_count
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [G15Afull, heterogeneousGao_N, gao_N, main10, ports10, auxiliary10,
      BaseC7.base_N, BaseC7.base_d, BaseC7.base_L]
  · rw [G15Afull, heterogeneousGao_d, gao_d, neutral10, ports10, BaseC7.base_d, BaseC7.base_eta]
  · rw [G15Afull, heterogeneousGao_L, auxiliary10Card, BaseC7.base_eta, Jplus_card,
      BaseC7.base_Xc_true, BaseC7.base_Xc_false]
  · rw [G15Afull, heterogeneousGao_eta, sibling_auxiliaryNeutral G10A G10A rfl rfl,
      neutral10Card, BaseC7.base_eta, outsideCount, BaseC7.base_Xc_true, BaseC7.base_Xc_false]
  · rw [G15Afull, heterogeneousGao_h, sibling_auxiliaryFoot G10A G10A rfl rfl true,
      h10, BaseC7.base_eta, Jplus_card, outsideCount, BaseC7.base_Xc_false]
  · rw [G15Afull, heterogeneousGao_v, sibling_auxiliaryFoot G10A G10A rfl rfl false,
      v10, BaseC7.base_eta, Jplus_card, outsideCount, BaseC7.base_Xc_true]

end ShannonBounds.C7Improvement
