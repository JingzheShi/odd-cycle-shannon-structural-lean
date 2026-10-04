import ExplorationC13FrontierR03.Capacity

namespace ShannonBounds.ExplorationC13FrontierR03.Capacity

set_option exponentiation.threshold 20000

theorem strict_decimal_integer :
    6302927403571109 ^ 522 < N * (1000000000000000 : Nat) ^ 522 := by native_decide

theorem strict_capacity_lower :
    (6.302927403571109 : ℝ) < shannonCapacity (SimpleGraph.cycleGraph 13) := by
  apply lt_of_lt_of_le _ capacity_root
  rw [show (6.302927403571109 : ℝ) =
    (6302927403571109 : ℝ) / 1000000000000000 by norm_num]
  rw [show ((1 : ℝ) / (522 : Nat)) = ((522 : Nat) : ℝ)⁻¹ by norm_num,
    Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) (by positivity),
    Real.rpow_natCast, div_pow, div_lt_iff₀ (by positivity)]
  exact_mod_cast strict_decimal_integer

end ShannonBounds.ExplorationC13FrontierR03.Capacity

#print axioms ShannonBounds.ExplorationC13FrontierR03.Capacity.strict_capacity_lower
