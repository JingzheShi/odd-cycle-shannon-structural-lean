import C7Improvement.G15Data
import C7Improvement.GaoProfile

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

attribute [local irreducible] G10 G10A G10D BaseC7.base Jplus

theorem G15het_profile : G15het.N = 49495055 ∧ G15het.d = 2504616 ∧
    G15het.L = 49433743 ∧ G15het.eta = 35275258 ∧
    (G15het.Xc true).card = 6703815 ∧ (G15het.Xc false).card = 7454670 := by
  obtain ⟨main10, ports10, auxiliary10, neutral10, h10, v10⟩ := G10_profile
  have neutral10Card : G10.Xstar.card = 105709 := neutral10
  have auxiliary10Card : G10.X.card = 134689 := auxiliary10
  have baseNeutral : BaseC7.base.Xstar.card = 322 := BaseC7.base_eta
  have outsideCount : (outside G10 Jplus).card = 27488 := C1_count
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [G15het, heterogeneousGao_N]
    rw [gao_N, main10, ports10, auxiliary10, BaseC7.base_N, BaseC7.base_d, BaseC7.base_L]
  · rw [G15het, heterogeneousGao_d]
    rw [gao_d, neutral10, ports10, BaseC7.base_d, BaseC7.base_eta]
  · rw [G15het, heterogeneousGao_L, auxiliary10Card, BaseC7.base_eta, Jplus_card,
      BaseC7.base_Xc_true, BaseC7.base_Xc_false]
  · rw [G15het, heterogeneousGao_eta, sibling_auxiliaryNeutral G10 G10 rfl rfl,
      neutral10Card, BaseC7.base_eta, outsideCount, BaseC7.base_Xc_true, BaseC7.base_Xc_false]
  · rw [G15het, heterogeneousGao_h, sibling_auxiliaryFoot G10 G10 rfl rfl true,
      h10, BaseC7.base_eta, Jplus_card, outsideCount, BaseC7.base_Xc_false]
  · rw [G15het, heterogeneousGao_v, sibling_auxiliaryFoot G10 G10 rfl rfl false,
      v10, BaseC7.base_eta, Jplus_card, outsideCount, BaseC7.base_Xc_true]

end ShannonBounds.C7Improvement
