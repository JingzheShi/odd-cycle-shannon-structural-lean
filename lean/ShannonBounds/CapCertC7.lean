/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.CertC7
import ShannonBounds.CapC7
import ShannonBounds.Decimal

/-!
# `Theta (C7) >= 3.258827985920007`

`CertC7.bound` is conditional on a port system whose seven families have the sizes in
`w0`.  The base system of `BaseC7` has exactly those sizes, all proved there.  Transporting
along `strongPower Cyc7 500 ≃g strongPower G5 100` gives the capacity bound.
-/

namespace ShannonBounds
namespace CapCertC7

open SimpleGraph

/-- The seven families of the `C7` base system have the sizes recorded in `w0`. -/
theorem base_fam_card : ∀ a, (BaseC7.base.fam a).card = CertC7.w0 a := by
  intro a
  cases a
  · rw [RichPortSystem.card_fam_B, BaseC7.base_N, BaseC7.base_d]; rfl
  · rw [RichPortSystem.card_fam_N, BaseC7.base_eta]; rfl
  · exact BaseC7.base_Xc_false
  · exact BaseC7.base_Xc_true
  · rw [RichPortSystem.card_fam_O, BaseC7.base_d]; rfl
  · rw [RichPortSystem.card_fam_H, BaseC7.base_d]; rfl
  · rw [RichPortSystem.card_fam_V, BaseC7.base_d]; rfl

/-- The independent set, in the `100`-th strong power of the base graph. -/
theorem alpha_G5_ge : CertC7.M ≤ (strongPower BaseC7.G5 100).indepNum :=
  CertC7.bound BaseC7.base base_fam_card

/-- `C7^(box 500)` is the `100`-th strong power of `C7^(box 5)`. -/
def iso500 : strongPower BaseC7.Cyc7 500 ≃g strongPower BaseC7.G5 100 :=
  (strongPower_mul_iso BaseC7.Cyc7 5 100).trans
    (strongPower_congr CapC7.G5_iso 100).symm

/-- The independent set, in `C7^(box 500)`. -/
theorem alpha_strongPower_ge :
    CertC7.M ≤ (strongPower BaseC7.Cyc7 500).indepNum := by
  rw [independenceNumber_iso iso500]
  exact alpha_G5_ge

/-- The capacity bound, in exact root form. -/
theorem shannonCapacity_Cyc_ge :
    ((CertC7.M : ℕ) : ℝ) ^ ((1 : ℝ) / (500 : ℕ)) ≤ shannonCapacity BaseC7.Cyc7 := by
  calc ((CertC7.M : ℕ) : ℝ) ^ ((1 : ℝ) / (500 : ℕ))
      ≤ (((strongPower BaseC7.Cyc7 500).indepNum : ℕ) : ℝ) ^ ((1 : ℝ) / (500 : ℕ)) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast alpha_strongPower_ge
    _ ≤ shannonCapacity BaseC7.Cyc7 :=
        shannonCapacity_ge_root BaseC7.Cyc7 500 (by norm_num)

theorem shannonCapacity_cycleGraph_ge :
    ((CertC7.M : ℕ) : ℝ) ^ ((1 : ℝ) / (500 : ℕ))
      ≤ shannonCapacity (SimpleGraph.cycleGraph 7) := by
  rw [← CapC7.Cyc_eq_cycleGraph]
  exact shannonCapacity_Cyc_ge

/-- **`Theta (cycleGraph 7) >= 3.258827985920007`**. -/
theorem shannonCapacity_cycleGraph_7_ge :
    (3.258827985920007 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) := by
  have h := shannonCapacity_cycleGraph_ge
  refine le_trans ?_ h
  rw [show ((3.258827985920007 : ℝ))
      = ((3258827985920007 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) by norm_num]
  exact Decimal.decimal_le (by norm_num) (by norm_num) (by native_decide) le_rfl

/-- The truncation is tight. -/
theorem tight :
    3258827985920007 ^ 500 ≤ CertC7.M * (10 ^ 15) ^ 500 ∧
      CertC7.M * (10 ^ 15) ^ 500 < 3258827985920008 ^ 500 := by
  constructor <;> native_decide

end CapCertC7
end ShannonBounds
