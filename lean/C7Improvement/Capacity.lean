import C7Improvement.LayeredNumbers
import ShannonBounds.Decimal

namespace ShannonBounds.C7Improvement

open BaseC7 SimpleGraph
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option exponentiation.threshold 20000
set_option synthInstance.maxSize 16000

attribute [local irreducible] simpleRule strongRule

theorem terminal_weight_congr (first second : Letter → ℕ) (equal : ∀ letter, first letter = second letter) :
    (∑ word ∈ K2.C, ∏ index : Fin 2, first (word index)) =
      ∑ word ∈ K2.C, ∏ index : Fin 2, second (word index) := by
  apply Finset.sum_congr rfl
  intro word memberWord
  apply Finset.prod_congr rfl
  intro index memberIndex
  exact equal (word index)

theorem alpha_Cyc7_280 : M280 ≤ (strongPower Cyc7 280).indepNum := by
  have actual := le_indepNum_multiCode (fun _ : Fin 2 => ∑ index : Fin 3, simpleDimensions index)
    (fun _ => simpleRule) K2
  have exactSize := (terminal_weight_congr simpleRule.w simpleRuleWeights simpleRule_weights).trans simple_layered_size
  rw [exactSize, simple_exponent] at actual
  exact actual

theorem alpha_Cyc7_300 : M300 ≤ (strongPower Cyc7 300).indepNum := by
  have actual := le_indepNum_multiCode (fun _ : Fin 2 => ∑ index : Fin 3, strongDimensions index)
    (fun _ => strongRule) K2
  have exactSize := (terminal_weight_congr strongRule.w strongRuleWeights strongRule_weights).trans strong_layered_size
  rw [exactSize, strong_exponent] at actual
  exact actual

theorem alpha_cycleGraph_280 : M280 ≤ (strongPower (cycleGraph 7) 280).indepNum := by
  rw [← CapC7.Cyc_eq_cycleGraph]
  exact alpha_Cyc7_280

theorem alpha_cycleGraph_300 : M300 ≤ (strongPower (cycleGraph 7) 300).indepNum := by
  rw [← CapC7.Cyc_eq_cycleGraph]
  exact alpha_Cyc7_300

theorem shannonCapacity_C7_ge_simple_root :
    (M280 : ℝ) ^ ((1 : ℝ) / 280) ≤ shannonCapacity (cycleGraph 7) := by
  calc
    _ ≤ ((strongPower (cycleGraph 7) 280).indepNum : ℝ) ^ ((1 : ℝ) / 280) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact_mod_cast alpha_cycleGraph_280
    _ ≤ shannonCapacity (cycleGraph 7) := shannonCapacity_ge_root (cycleGraph 7) 280 (by norm_num)

theorem shannonCapacity_C7_ge_strong_root :
    (M300 : ℝ) ^ ((1 : ℝ) / 300) ≤ shannonCapacity (cycleGraph 7) := by
  calc
    _ ≤ ((strongPower (cycleGraph 7) 300).indepNum : ℝ) ^ ((1 : ℝ) / 300) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact_mod_cast alpha_cycleGraph_300
    _ ≤ shannonCapacity (cycleGraph 7) := shannonCapacity_ge_root (cycleGraph 7) 300 (by norm_num)

theorem decimal_lt {numerator denominator size dimension : ℕ} {capacity : ℝ}
    (positiveDenominator : 0 < denominator) (positiveDimension : 0 < dimension)
    (strictPower : numerator ^ dimension < size * denominator ^ dimension)
    (rootBound : (size : ℝ) ^ ((1 : ℝ) / (dimension : ℝ)) ≤ capacity) :
    (numerator : ℝ) / (denominator : ℝ) < capacity := by
  refine lt_of_lt_of_le ?_ rootBound
  rw [show ((1 : ℝ) / (dimension : ℝ)) = (dimension : ℝ)⁻¹ by norm_num,
    Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) (by exact_mod_cast positiveDimension),
    Real.rpow_natCast, div_pow, div_lt_iff₀ (by positivity)]
  exact_mod_cast strictPower

theorem shannonCapacity_C7_gt_simple :
    (3.258834362237710 : ℝ) < shannonCapacity (cycleGraph 7) := by
  rw [show (3.258834362237710 : ℝ) = ((3258834362237710 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) by norm_num]
  exact decimal_lt (by norm_num) (by norm_num) simple_strict_decimal_check shannonCapacity_C7_ge_simple_root

theorem shannonCapacity_C7_gt_strong :
    (3.258834805519757 : ℝ) < shannonCapacity (cycleGraph 7) := by
  rw [show (3.258834805519757 : ℝ) = ((3258834805519757 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) by norm_num]
  exact decimal_lt (by norm_num) (by norm_num) strong_strict_decimal_check shannonCapacity_C7_ge_strong_root

theorem root_power_cross (size dimension multiplier : ℕ) (positiveDimension : 0 < dimension) :
    ((size : ℝ) ^ ((1 : ℝ) / (dimension : ℝ))) ^ ((dimension * multiplier : ℕ) : ℝ) =
      (size : ℝ) ^ (multiplier : ℝ) := by
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  have nonzeroDimension : (dimension : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem root_lt_of_cross_power {first second firstDimension secondDimension : ℕ}
    (firstPositive : 0 < firstDimension) (secondPositive : 0 < secondDimension)
    (strictPower : first ^ secondDimension < second ^ firstDimension) :
    (first : ℝ) ^ ((1 : ℝ) / (firstDimension : ℝ)) <
      (second : ℝ) ^ ((1 : ℝ) / (secondDimension : ℝ)) := by
  have firstPower := root_power_cross first firstDimension secondDimension firstPositive
  have secondPower := root_power_cross second secondDimension firstDimension secondPositive
  rw [Nat.mul_comm secondDimension firstDimension] at secondPower
  apply (Real.rpow_lt_rpow_iff (by positivity) (by positivity)
    (show (0 : ℝ) < ((firstDimension * secondDimension : ℕ) : ℝ) by positivity)).mp
  rw [firstPower, secondPower, Real.rpow_natCast, Real.rpow_natCast]
  exact_mod_cast strictPower

theorem simple_root_gt_baseline :
    (baseline500Size : ℝ) ^ ((1 : ℝ) / 500) < (M280 : ℝ) ^ ((1 : ℝ) / 280) :=
  root_lt_of_cross_power (by norm_num) (by norm_num) simple_beats_baseline_check

theorem strong_root_gt_simple :
    (M280 : ℝ) ^ ((1 : ℝ) / 280) < (M300 : ℝ) ^ ((1 : ℝ) / 300) :=
  root_lt_of_cross_power (by norm_num) (by norm_num) strong_beats_simple_check

end ShannonBounds.C7Improvement
