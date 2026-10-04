/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/

import ShannonBounds.Defs

/-!
# From a root to the value stated in `Main.lean`

Each capacity bound is proved in the form `α(Cₙ^⊠p) ^ (1/p) ≤ Θ(Cₙ)` for an
explicit independent set.  `decimal_le` converts that to the truncated value
`Main.lean` states: comparing `a / b` with `N ^ (1/p)` is the integer inequality
`a ^ p ≤ N * b ^ p`, which `native_decide` evaluates directly.
-/

namespace ShannonBounds
namespace Decimal

open SimpleGraph

set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

/-- Comparing a decimal `a / b` with a bound of the form `N ^ (1/p)` comes
down to the integer inequality `a ^ p ≤ N * b ^ p`. -/
theorem decimal_le {a b N p : ℕ} {c : ℝ} (hb : 0 < b) (hp : 0 < p)
    (hpow : a ^ p ≤ N * b ^ p)
    (hcap : ((N : ℕ) : ℝ) ^ ((1 : ℝ) / (p : ℕ)) ≤ c) :
    ((a : ℕ) : ℝ) / ((b : ℕ) : ℝ) ≤ c := by
  refine le_trans ?_ hcap
  have hb' : (0 : ℝ) < (b : ℕ) := by exact_mod_cast hb
  rw [show ((1 : ℝ) / (p : ℕ)) = ((p : ℕ) : ℝ)⁻¹ by norm_num,
      Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by exact_mod_cast hp),
      Real.rpow_natCast, div_pow, div_le_iff₀ (by positivity)]
  exact_mod_cast hpow

end Decimal
end ShannonBounds
