import C7Improvement.Atoms10
import C7Improvement.Histogram

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 G15X neutralNear restNear inNeutral10 inRest10

theorem rest_eq_classes {Point : Type*} [DecidableEq Point] {graph : SimpleGraph Point}
    [DecidableRel graph.Adj] (system : RichPortSystem graph) :
    system.X \ system.Xstar = system.Xc false ∪ system.Xc true := by
  ext point
  rw [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨member, notNeutral⟩
    by_cases memberFalse : point ∈ system.Xc false
    · exact Or.inl memberFalse
    by_cases memberTrue : point ∈ system.Xc true
    · exact Or.inr memberTrue
    exact False.elim (notNeutral (system.mem_Xstar.mpr ⟨member, memberFalse, memberTrue⟩))
  · rintro (member | member)
    · exact ⟨system.Xc_subset_X false member, fun neutral => (system.mem_Xstar.mp neutral).2.1 member⟩
    · exact ⟨system.Xc_subset_X true member, fun neutral => (system.mem_Xstar.mp neutral).2.2 member⟩

theorem G10_rest : G10.X \ G10.Xstar =
    (BaseC7.base.Xstar ×ˢ (BaseC7.base.X \ BaseC7.base.Xstar)) ∪
      ((BaseC7.base.X \ BaseC7.base.Xstar) ×ˢ BaseC7.base.Xstar) := by
  rw [rest_eq_classes G10, G10, gao_Xc, gao_Xc, rest_eq_classes BaseC7.base]
  simp only [Bool.not_false, Bool.not_true, Finset.product_union, Finset.union_product,
    Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]

theorem inRest10_spec (point : BaseC7.Code × BaseC7.Code) :
    inRest10 point = true ↔ near (strongProd G5 G5) (G10.X \ G10.Xstar) point := by
  rw [G10_rest, near_union, near_product, near_product]
  simp only [inRest10, Bool.or_eq_true, Bool.and_eq_true, neutralNear_spec, restNear_spec]

def ref15Left : Fin 2 → Finset (BaseC7.Code × BaseC7.Code) := ![G10.Xstar, G10.X \ G10.Xstar]

def ref15Right : Fin 2 → Finset BaseC7.Code := ![BaseC7.base.Xstar, BaseC7.base.X \ BaseC7.base.Xstar]

theorem ref15_eq : referenceUnion ref15Left ref15Right = G15X.Xstar := by
  rw [G15X, gao_Xstar]
  ext point
  simp only [referenceUnion, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨index, member⟩
    fin_cases index
    · exact Or.inl member
    · exact Or.inr member
  · rintro (member | member)
    · exact ⟨0, member⟩
    · exact ⟨1, member⟩

theorem flags10_eq : flags10 = neighborhoodFlags (GL := strongProd G5 G5) ref15Left := by
  funext point index
  apply Bool.eq_iff_iff.mpr
  fin_cases index
  · change (inNeutral10 point = true) ↔ (decide (near (strongProd G5 G5) G10.Xstar point) = true)
    simpa only [decide_eq_true_eq] using inNeutral10_spec point
  · change (inRest10 point = true) ↔ (decide (near (strongProd G5 G5) (G10.X \ G10.Xstar) point) = true)
    simpa only [decide_eq_true_eq] using inRest10_spec point

theorem flags5_eq : flags5 = neighborhoodFlags (GL := G5) ref15Right := by
  funext point index
  apply Bool.eq_iff_iff.mpr
  fin_cases index
  · change (neutralNear point = true) ↔ (decide (near G5 BaseC7.base.Xstar point) = true)
    simpa only [decide_eq_true_eq] using neutralNear_spec point
  · change (restNear point = true) ↔ (decide (near G5 (BaseC7.base.X \ BaseC7.base.Xstar) point) = true)
    simpa only [decide_eq_true_eq] using restNear_spec point

end ShannonBounds.C7Improvement
