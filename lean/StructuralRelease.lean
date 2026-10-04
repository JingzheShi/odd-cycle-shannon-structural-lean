import C7Improvement.Capacity
import ExplorationC13FrontierR03.StrictDisplay
import ActualRegion
import ExplorationC7.Correlated.Witness

namespace StructuralRelease

theorem c7_strict :
    (3.258834805519757 : ℝ) < ShannonBounds.shannonCapacity (SimpleGraph.cycleGraph 7) :=
  ShannonBounds.C7Improvement.shannonCapacity_C7_gt_strong

theorem c13_strict :
    (6.302927403571109 : ℝ) < ShannonBounds.shannonCapacity (SimpleGraph.cycleGraph 13) :=
  ShannonBounds.ExplorationC13FrontierR03.Capacity.strict_capacity_lower

theorem c13_region (a b c : Nat)
    (hab : a + b ≤ 169) (hac : a + c ≤ 169)
    (hx : 169 - a - b < 13) (hy : 169 - a - c < 13) :
    (∃ f g h : C13Structure.H → Bool,
      ShannonBounds.BaseC13.G6.IsIndepSet ↑(C13Structure.physicalCode f g h) ∧
      (C13Structure.fiberCode 0 f).card = a ∧
      b ≤ (C13Structure.fiberCode 1 g).card ∧
      c ≤ (C13Structure.fiberCode 2 h).card) ↔
    (a ≤ (169 - a - c) * (169 - a - b) ∨
      169 - a ≤ (169 - a - c) * (169 - a - b)) :=
  C13Structure.actual_star_region_iff a b c hab hac hx hy

theorem c13_example :
    (SimpleGraph.strongPower (SimpleGraph.cycleGraph 13) 6).IsIndepSet
      ↑C13Structure.cycleCode ∧ C13Structure.cycleCode.card = 240 :=
  ⟨C13Structure.cycleCode_independent, C13Structure.cycleCode_card⟩

theorem c7_illustration :
    (SimpleGraph.strongPower ShannonBounds.BaseC7.Cyc7 3).IsIndepSet
      ↑(ShannonBounds.ExplorationC7.Correlated.first ∪
        ShannonBounds.ExplorationC7.Correlated.second) :=
  ShannonBounds.ExplorationC7.Correlated.actual_union_independent

end StructuralRelease
