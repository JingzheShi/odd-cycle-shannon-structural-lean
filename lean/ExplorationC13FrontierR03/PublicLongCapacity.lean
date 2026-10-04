/-
Contributed in 2026 by Griffin Long, with the AI agent agent-afk, as an addition to the
ShannonBounds framework of Pjotr Buys, Sven Polak and Jeroen Zuiddam (who did not write this
file). Released under Apache 2.0 license as described in the file LICENSE.
(This file: a variant of `CapCertC13.lean` for the schedule of `PublicLong.lean`.)
-/
import ExplorationC13FrontierR03.PublicLong
import ShannonBounds.CapC13
import ShannonBounds.Decimal

/-!
# `Theta (C13) >= 6.302927071589786`

`PublicLong.bound` is conditional on a port system whose seven families have the sizes in
`w0`.  The base system of `BaseC13` has exactly those sizes, all proved there.  Transporting
along `strongPower Cyc13 522 ≃g strongPower G6 87` gives the capacity bound.
-/

namespace ShannonBounds.ExplorationC13FrontierR03
namespace PublicLongCapacity

open SimpleGraph

/-- The seven families of the `C13` base system have the sizes recorded in `w0`. -/
theorem base_fam_card : ∀ a, (BaseC13.base.fam a).card = PublicLong.w0 a := by
  intro a
  cases a
  · rw [RichPortSystem.card_fam_B, BaseC13.base_N, BaseC13.base_d]; rfl
  · rw [RichPortSystem.card_fam_N, BaseC13.base_eta]; rfl
  · exact BaseC13.base_Xc_card false
  · exact BaseC13.base_Xc_card true
  · rw [RichPortSystem.card_fam_O, BaseC13.base_d]; rfl
  · rw [RichPortSystem.card_fam_H, BaseC13.base_d]; rfl
  · rw [RichPortSystem.card_fam_V, BaseC13.base_d]; rfl

/-- The independent set, in the `87`-th strong power of the base graph. -/
theorem alpha_G6_ge : PublicLong.M ≤ (strongPower BaseC13.G6 87).indepNum :=
  PublicLong.bound BaseC13.base base_fam_card

/-- `C13^(box 522)` is the `87`-th strong power of `C13^(box 6)`. -/
def iso522 : strongPower BaseC13.Cyc13 522 ≃g strongPower BaseC13.G6 87 :=
  (strongPower_mul_iso BaseC13.Cyc13 6 87).trans
    (strongPower_congr CapC13.G6_iso 87).symm

/-- The independent set, in `C13^(box 522)`. -/
theorem alpha_strongPower_ge :
    PublicLong.M ≤ (strongPower BaseC13.Cyc13 522).indepNum := by
  rw [independenceNumber_iso iso522]
  exact alpha_G6_ge

/-- The capacity bound, in exact root form. -/
theorem shannonCapacity_Cyc_ge :
    ((PublicLong.M : ℕ) : ℝ) ^ ((1 : ℝ) / (522 : ℕ)) ≤ shannonCapacity BaseC13.Cyc13 := by
  calc ((PublicLong.M : ℕ) : ℝ) ^ ((1 : ℝ) / (522 : ℕ))
      ≤ (((strongPower BaseC13.Cyc13 522).indepNum : ℕ) : ℝ) ^ ((1 : ℝ) / (522 : ℕ)) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast alpha_strongPower_ge
    _ ≤ shannonCapacity BaseC13.Cyc13 :=
        shannonCapacity_ge_root BaseC13.Cyc13 522 (by norm_num)

theorem shannonCapacity_cycleGraph_ge :
    ((PublicLong.M : ℕ) : ℝ) ^ ((1 : ℝ) / (522 : ℕ))
      ≤ shannonCapacity (SimpleGraph.cycleGraph 13) := by
  rw [← CapC13.Cyc_eq_cycleGraph]
  exact shannonCapacity_Cyc_ge

/-- **`Theta (cycleGraph 13) >= 6.302927071589786`**. -/
theorem shannonCapacity_cycleGraph_13_ge :
    (6.302927071589786 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 13) := by
  have h := shannonCapacity_cycleGraph_ge
  refine le_trans ?_ h
  rw [show ((6.302927071589786 : ℝ))
      = ((6302927071589786 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) by norm_num]
  exact Decimal.decimal_le (by norm_num) (by norm_num) (by native_decide) le_rfl

/-- The truncation is tight. -/
theorem tight :
    6302927071589786 ^ 522 ≤ PublicLong.M * (10 ^ 15) ^ 522 ∧
      PublicLong.M * (10 ^ 15) ^ 522 < 6302927071589787 ^ 522 := by
  constructor <;> native_decide

/-- Strictly improves the bound of `CapCertC13` (BPZ). -/
theorem improves : (6.302926729310108 : ℝ) < 6.302927071589786 := by norm_num


/-- Strictly improves the bound of Protti, c11-shannon-capacity-lower-bound v0.5.0, `C13R8D522.capacity_lower`. -/
theorem improves_1 : (6.302927046770772 : ℝ) < 6.302927071589786 := by norm_num

end PublicLongCapacity
end ShannonBounds.ExplorationC13FrontierR03
