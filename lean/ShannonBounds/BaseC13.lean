/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
The assembled `RichPortSystem` and its four parameters.

All four parameters are `169 * (a count on cosets)`:

    N   = 169 * |S|   = 169 * 370 = 62530      d   = 169 * |S_P| = 169 * 6 = 1014
    L   = 169 * |S_X| = 169 * 370 = 62530      eta = L - 169 * (|SF0| + |SF1|) = 60502
-/
import ShannonBounds.BaseC13Foot
import ShannonBounds.BaseC13PIndep
import ShannonBounds.BaseC13Priv

namespace ShannonBounds
namespace BaseC13

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

/-! ### The assembled system -/

/-- **The base system on `C13^(box 6)`.** -/
def base : RichPortSystem G6 where
  I := Iset
  hI := isIndepSet_I
  ports := portsSet
  hports := h_ports
  ep := bep
  side := bside
  hep_parent := h_ep_parent
  halt_not := h_alt_not
  hprivate := h_private
  hep_conflict := h_ep_conflict
  halt_inj := h_alt_inj
  hP_indep := h_P_indep
  X := Xset
  hX := isIndepSet_X
  hsep := h_sep

/-! ### The four parameters -/

theorem base_N : base.N = 62530 := by
  change Iset.card = 62530
  exact Icard

theorem base_d : base.d = 1014 := by
  change portsSet.card = 1014
  exact portsCard

theorem base_L : base.L = 62530 := by
  change Xset.card = 62530
  exact Xcard

/-- **The footprint is exactly six `K`-cosets.** -/
lemma Xc_eq (c : Bool) : base.Xc c = Pre (SFraw c) := by
  ext x
  rw [RichPortSystem.mem_Xc, mem_Pre (SFbound c)]
  exact foot_iff c x

theorem base_Xc_card (c : Bool) : (base.Xc c).card = 1014 := by
  rw [Xc_eq, card_Pre (SFbound c) (SFnodup c), SFlen]

theorem base_eta : base.eta = 60502 := by
  change (Xset \ (base.Xc false ∪ base.Xc true)).card = 60502
  have hsub : base.Xc false ∪ base.Xc true ⊆ Xset := by
    change base.Xc false ∪ base.Xc true ⊆ base.X
    exact Finset.union_subset (base.Xc_subset_X false) (base.Xc_subset_X true)
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_union_of_disjoint base.Xc_disjoint,
    base_Xc_card, base_Xc_card, Xcard]

end BaseC13
end ShannonBounds
