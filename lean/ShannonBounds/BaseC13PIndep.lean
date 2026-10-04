/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# Independence of the two transversals

* `P_0` is the port set itself (every side is `false`), and `ports subset I` with `I`
  independent, so `P_0` is independent.
* `P_1 = sigma^{-1}(S_A)` is a union of six `K`-cosets, and is independent because no
  `Delta`-translate of one of the six alternative cosets is again one of them:
  `6 * 482` checks (`SAindCheck`), by the same argument that makes `I` independent.
-/
import ShannonBounds.BaseC13Ports

namespace ShannonBounds
namespace BaseC13

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

/-- The alternative transversal is an independent set. -/
theorem isIndepSet_alt : G6.IsIndepSet ((Pre SAraw : Finset Code) : Set Code) :=
  indepPre SAbound (fun x => SAraw.contains x)
    (fun _ hs => List.contains_iff_mem.mpr hs)
    (fun q hq e he => by
      simpa using List.all_eq_true.mp (List.all_eq_true.mp SAindCheck q hq) e he)

theorem h_P_indep : ∀ c : Bool, ∀ r ∈ portsSet, ∀ s ∈ portsSet, r ≠ s →
    ¬ conflict G6 (bep c r) (bep c s) := by
  intro c r hr s hs hrs hc
  cases c
  · -- `P_0` is the port set, which sits inside the independent set `I`
    rw [bep_false, bep_false] at hc
    rcases hc with he | hadj
    · exact hrs he
    · exact isIndepSet_I (Finset.mem_coe.mpr (h_ports hr))
        (Finset.mem_coe.mpr (h_ports hs)) hrs hadj
  · -- `P_1` is a union of six cosets, independent by `SAindCheck`
    have hne : bep true r ≠ bep true s := by
      intro he
      exact hrs (h_alt_inj r hr s hs (by rw [bside_not, bside_not]; exact he))
    rcases hc with he | hadj
    · exact hne he
    · exact isIndepSet_alt (Finset.mem_coe.mpr (bep_true_mem_alt hr))
        (Finset.mem_coe.mpr (bep_true_mem_alt hs)) hne hadj

end BaseC13
end ShannonBounds
