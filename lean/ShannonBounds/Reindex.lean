/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.Layered
import ShannonBounds.PortRealisation

/-!
# Reindexing a realisation along a symmetry of the separation table

A realisation attaches an independent set to each letter, with separated letters receiving
separated sets.  Nothing in that asks the letters to be told apart in any other way, so any
permutation of the alphabet preserving `sep` carries a realisation to another realisation of
the same system, in the *same* graph, with the weights permuted.

A schedule may feed a realisation to one child of a node and its reindexing to another, so
both weight vectors are available at once.

For the seven-letter system of `PortRealisation.lean` the permutation used below is
`sigma = (A D)(H V)`, which fixes `B`, `N` and `O`; it is the global flip of the side vector
of the underlying port system.
-/

namespace ShannonBounds

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {A : Type*} [Fintype A] {sep : A → A → Bool}
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Reindex a realisation along a permutation of the alphabet preserving `sep`. -/
def Realisation.reindex (R : Realisation A sep G) (e : A ≃ A)
    (he : ∀ a b, sep (e a) (e b) = sep a b) : Realisation A sep G where
  P a := R.P (e a)
  hindep a := R.hindep (e a)
  hsep a b h := R.hsep (e a) (e b) (by rw [he]; exact h)

@[simp] lemma Realisation.w_reindex (R : Realisation A sep G) (e : A ≃ A)
    (he : ∀ a b, sep (e a) (e b) = sep a b) (a : A) :
    (R.reindex e he).w a = R.w (e a) := rfl

/-- The automorphism `(A D)(H V)` of the seven-letter separation table. -/
def Letter.sigma : Letter ≃ Letter where
  toFun
    | .B => .B | .N => .N | .A => .D | .D => .A | .O => .O | .H => .V | .V => .H
  invFun
    | .B => .B | .N => .N | .A => .D | .D => .A | .O => .O | .H => .V | .V => .H
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

/-- `sigma` preserves the separation table; since it is an involution, it is an
automorphism. -/
theorem Letter.sigma_sep (a b : Letter) :
    Letter.sep (Letter.sigma a) (Letter.sigma b) = Letter.sep a b := by
  cases a <;> cases b <;> rfl

end ShannonBounds
