/-
Contributed in 2026 by Griffin Long, with the AI agent agent-afk, as an addition to the
ShannonBounds framework of Pjotr Buys, Sven Polak and Jeroen Zuiddam (who did not write this
file). Released under Apache 2.0 license as described in the file LICENSE.
(This file: the arity-`3` analogue of `DagTail.code4` / `DagTail.sum_code4`, for terminal
codes with three positions such as `TerminalCodes.K3a`.)
-/
import ExplorationC13FrontierR03.DagTail

namespace ShannonBounds.ExplorationC13FrontierR03
namespace DagTail

open SimpleGraph

/-- The size of the independent set of an arity-`3` terminal code. -/
def code3 (K : Code Letter Letter.sep 3) (s0 s1 s2 : Sizes) : Nat :=
  ∑ x ∈ K.C, s0.get (x 0) * s1.get (x 1) * s2.get (x 2)

variable {α : Type*} [Fintype α] [DecidableEq α]
  {G : SimpleGraph α} [DecidableRel G.Adj]

omit [Fintype α] in
/-- An arity-`3` terminal code applied to children with known sizes. -/
lemma sum_code3 (K : Code Letter Letter.sep 3) {e : Fin 3 → ℕ}
    (ch : (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (e i)))
    (s0 s1 s2 : Sizes) (h0 : ∀ b, (ch 0).w b = s0.get b) (h1 : ∀ b, (ch 1).w b = s1.get b)
    (h2 : ∀ b, (ch 2).w b = s2.get b) :
    (∑ x ∈ K.C, ∏ i, (ch i).w (x i)) = code3 K s0 s1 s2 := by
  rw [code3]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fin.prod_univ_three, h0, h1, h2]

end DagTail
end ShannonBounds.ExplorationC13FrontierR03
