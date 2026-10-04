import C7Improvement.C4Masks
import C7Improvement.C4Atoms

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 10000
set_option maxHeartbeats 300000

attribute [local irreducible] BaseC7.base G10 G10A Jplus JqList JnList
attribute [local irreducible] neutralNear restNear inNeutral10 inRest10 aNear dNear jqIndex jnIndex

theorem left10Flags_spec (point : BaseC7.Code × BaseC7.Code) (index : Fin 2) :
    flags10 point index = true ↔ near (strongProd G5 G5) (tenAtomSet (tenLeftIndices index)) point := by
  fin_cases index
  · change inNeutral10 point = true ↔ near (strongProd G5 G5) G10.Xstar point
    exact inNeutral10_spec point
  · change inRest10 point = true ↔ near (strongProd G5 G5) (G10.X \ G10.Xstar) point
    exact inRest10_spec point

theorem left5Flags_spec (point : BaseC7.Code) (index : Fin 2) :
    flags5 point index = true ↔ near G5 (fiveAtomSet (fiveLeftIndices index)) point := by
  fin_cases index
  · change neutralNear point = true ↔ near G5 BaseC7.base.Xstar point
    exact neutralNear_spec point
  · change restNear point = true ↔ near G5 (BaseC7.base.X \ BaseC7.base.Xstar) point
    exact restNear_spec point

theorem right10Flags_spec (point : BaseC7.Code × BaseC7.Code) (index : Fin 6) :
    right10Flags point index = true ↔ near (strongProd G5 G5) (tenAtomSet (tenRightIndices index)) point := by
  fin_cases index
  · change inNeutral10 point = true ↔ near (strongProd G5 G5) G10.Xstar point
    exact inNeutral10_spec point
  · change inRest10 point = true ↔ near (strongProd G5 G5) (G10.X \ G10.Xstar) point
    exact inRest10_spec point
  · change jqIndex.query point = true ↔ near (strongProd G5 G5) (outside G10 Jplus) point
    rw [jqIndex, packedIndex_graph_spec, JqList_eq]
  · change jnIndex.query point = true ↔ near (strongProd G5 G5) (inside G10 Jplus) point
    rw [jnIndex, packedIndex_graph_spec, JnList_eq]
  · change ((neutralNear point.1 && aNear point.2) || (aNear point.1 && neutralNear point.2)) = true ↔
      near (strongProd G5 G5) (G10A.Xc true) point
    rw [G10A, gao_Xc, flip_Xstar, flip_Xc, near_union, near_product, near_product]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_true, neutralNear_spec, aNear_spec]
  · change ((neutralNear point.1 && dNear point.2) || (dNear point.1 && neutralNear point.2)) = true ↔
      near (strongProd G5 G5) (G10A.Xc false) point
    rw [G10A, gao_Xc, flip_Xstar, flip_Xc, near_union, near_product, near_product]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_false, neutralNear_spec, dNear_spec]

theorem right5Flags_spec (point : BaseC7.Code) (index : Fin 3) :
    right5Flags point index = true ↔ near G5 (fiveAtomSet (fiveRightIndices index)) point := by
  fin_cases index
  · change neutralNear point = true ↔ near G5 BaseC7.base.Xstar point
    exact neutralNear_spec point
  · change aNear point = true ↔ near G5 (BaseC7.base.Xc false) point
    exact aNear_spec point
  · change dNear point = true ↔ near G5 (BaseC7.base.Xc true) point
    exact dNear_spec point

end ShannonBounds.C7Improvement
