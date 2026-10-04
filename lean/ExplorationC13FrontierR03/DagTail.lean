/-
Contributed in 2026 by Griffin Long, with the AI agent agent-afk, as an addition to the
ShannonBounds framework of Pjotr Buys, Sven Polak and Jeroen Zuiddam (who did not write this
file). Released under Apache 2.0 license as described in the file LICENSE.
(This file: generic helpers for DAG schedules with several long homogeneous tails; it only
uses `Realisation.multiSubst` and `w_multiSubst` from `Layered.lean`.)
-/
import ShannonBounds.PortRealisation
import ShannonBounds.Layered

/-!
# Iterated tails and size bookkeeping for DAG schedules

A schedule node `multiSubst e ch S` has, letter by letter, the size
`∑ x ∈ S.T a, ∏ i, (ch i).w (x i)` (`w_multiSubst`).  This file packages that computation
on a strict seven-field record `Sizes` (so that evaluating a long chain inside `native_decide`
is linear in its length) and proves, once and for all:

* `w_node2`, `w_node3`: a node has the sizes `node2`/`node3` of its children's sizes;
* `tailIter S X Z1 Z2 n`: the `n`-fold tail `y ↦ S (y, Z1, Z2)` started at `y = X`, a
  realisation in `G^(box (e0 + n (k1 + k2)))`, defined by structural recursion on `n`;
* `w_tailIter`: by induction on `n`, its sizes are `tailW S sX s1 s2 n`.

A certificate then instantiates `tailIter` once per branch, with its own start node and length.
-/

namespace ShannonBounds.ExplorationC13FrontierR03
namespace DagTail

open SimpleGraph

/-- The seven sizes, as a strict record. -/
structure Sizes where
  b : Nat
  n : Nat
  a : Nat
  d : Nat
  o : Nat
  h : Nat
  v : Nat

/-- Read off a size. -/
def Sizes.get (s : Sizes) : Letter → Nat
  | .B => s.b
  | .N => s.n
  | .A => s.a
  | .D => s.d
  | .O => s.o
  | .H => s.h
  | .V => s.v

/-- Tabulate a size function. -/
def Sizes.ofFun (f : Letter → Nat) : Sizes :=
  ⟨f .B, f .N, f .A, f .D, f .O, f .H, f .V⟩

lemma Sizes.get_ofFun (f : Letter → Nat) (a : Letter) : (Sizes.ofFun f).get a = f a := by
  cases a <;> rfl

/-- The sizes of an arity-`2` node, from the sizes of its children. -/
def node2 (S : Subst Letter Letter.sep 2) (s0 s1 : Sizes) : Sizes :=
  Sizes.ofFun fun a => ∑ x ∈ S.T a, s0.get (x 0) * s1.get (x 1)

/-- The sizes of an arity-`3` node, from the sizes of its children. -/
def node3 (S : Subst Letter Letter.sep 3) (s0 s1 s2 : Sizes) : Sizes :=
  Sizes.ofFun fun a => ∑ x ∈ S.T a, s0.get (x 0) * s1.get (x 1) * s2.get (x 2)

/-- The size of the independent set of an arity-`4` terminal code. -/
def code4 (K : Code Letter Letter.sep 4) (s0 s1 s2 s3 : Sizes) : Nat :=
  ∑ x ∈ K.C, s0.get (x 0) * s1.get (x 1) * s2.get (x 2) * s3.get (x 3)

/-- The sizes of the `n`-fold tail `y ↦ S (y, z1, z2)` started at `y = s`. -/
def tailW (S : Subst Letter Letter.sep 3) (s s1 s2 : Sizes) : ℕ → Sizes
  | 0 => s
  | n + 1 => node3 S (tailW S s s1 s2 n) s1 s2

variable {α : Type*} [Fintype α] [DecidableEq α]
  {G : SimpleGraph α} [DecidableRel G.Adj]

/-- Transport a realisation along an equality of exponents. -/
def castR {m n : ℕ} (h : m = n) (R : Realisation Letter Letter.sep (SimpleGraph.strongPower G m)) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G n) :=
  h ▸ R

omit [Fintype α] in
lemma w_castR {m n : ℕ} (h : m = n)
    (R : Realisation Letter Letter.sep (SimpleGraph.strongPower G m)) (a : Letter) :
    (castR h R).w a = R.w a := by
  subst h; rfl

/-- An arity-`2` node has the sizes `node2` of its children's sizes. -/
lemma w_node2 (S : Subst Letter Letter.sep 2) {e : Fin 2 → ℕ}
    (ch : (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (e i)))
    (s0 s1 : Sizes) (h0 : ∀ b, (ch 0).w b = s0.get b) (h1 : ∀ b, (ch 1).w b = s1.get b)
    (a : Letter) : (Realisation.multiSubst e ch S).w a = (node2 S s0 s1).get a := by
  rw [w_multiSubst, node2, Sizes.get_ofFun]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fin.prod_univ_two, h0, h1]

/-- An arity-`3` node has the sizes `node3` of its children's sizes. -/
lemma w_node3 (S : Subst Letter Letter.sep 3) {e : Fin 3 → ℕ}
    (ch : (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (e i)))
    (s0 s1 s2 : Sizes) (h0 : ∀ b, (ch 0).w b = s0.get b) (h1 : ∀ b, (ch 1).w b = s1.get b)
    (h2 : ∀ b, (ch 2).w b = s2.get b)
    (a : Letter) : (Realisation.multiSubst e ch S).w a = (node3 S s0 s1 s2).get a := by
  rw [w_multiSubst, node3, Sizes.get_ofFun]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fin.prod_univ_three, h0, h1, h2]

omit [Fintype α] in
/-- An arity-`4` terminal code applied to children with known sizes. -/
lemma sum_code4 (K : Code Letter Letter.sep 4) {e : Fin 4 → ℕ}
    (ch : (i : Fin 4) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (e i)))
    (s0 s1 s2 s3 : Sizes) (h0 : ∀ b, (ch 0).w b = s0.get b) (h1 : ∀ b, (ch 1).w b = s1.get b)
    (h2 : ∀ b, (ch 2).w b = s2.get b) (h3 : ∀ b, (ch 3).w b = s3.get b) :
    (∑ x ∈ K.C, ∏ i, (ch i).w (x i)) = code4 K s0 s1 s2 s3 := by
  rw [code4]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fin.prod_univ_four, h0, h1, h2, h3]

/-- The child exponents of a tail step. -/
def tailE (e0 k1 k2 n : ℕ) : Fin 3 → ℕ := Fin.cases (e0 + n * (k1 + k2)) (Fin.cases k1 (fun _ => k2))

lemma sum_tailE (e0 k1 k2 n : ℕ) : ∑ i, tailE e0 k1 k2 n i = e0 + (n + 1) * (k1 + k2) := by
  rw [Fin.sum_univ_three]
  show e0 + n * (k1 + k2) + k1 + k2 = e0 + (n + 1) * (k1 + k2)
  ring

lemma tailE_zero (e0 k1 k2 : ℕ) : e0 = e0 + 0 * (k1 + k2) := by ring

/-- The children of a tail step: the previous tail node and the two fixed children. -/
def tailCh {e0 k1 k2 : ℕ} (n : ℕ)
    (Y : Realisation Letter Letter.sep (SimpleGraph.strongPower G (e0 + n * (k1 + k2))))
    (Z1 : Realisation Letter Letter.sep (SimpleGraph.strongPower G k1))
    (Z2 : Realisation Letter Letter.sep (SimpleGraph.strongPower G k2)) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (tailE e0 k1 k2 n i)) :=
  Fin.cases Y (Fin.cases Z1 (fun _ => Z2))

/-- **The iterated tail.**  `tailIter S X Z1 Z2 0 = X` and
`tailIter S X Z1 Z2 (n+1) = S (tailIter S X Z1 Z2 n, Z1, Z2)`. -/
def tailIter (S : Subst Letter Letter.sep 3) {e0 k1 k2 : ℕ}
    (X : Realisation Letter Letter.sep (SimpleGraph.strongPower G e0))
    (Z1 : Realisation Letter Letter.sep (SimpleGraph.strongPower G k1))
    (Z2 : Realisation Letter Letter.sep (SimpleGraph.strongPower G k2)) :
    (n : ℕ) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (e0 + n * (k1 + k2)))
  | 0 => castR (tailE_zero e0 k1 k2) X
  | n + 1 => castR (sum_tailE e0 k1 k2 n)
      (Realisation.multiSubst (tailE e0 k1 k2 n) (tailCh n (tailIter S X Z1 Z2 n) Z1 Z2) S)

/-- **The tail induction.**  The `n`-fold tail has the sizes `tailW S sX s1 s2 n`. -/
lemma w_tailIter (S : Subst Letter Letter.sep 3) {e0 k1 k2 : ℕ}
    (X : Realisation Letter Letter.sep (SimpleGraph.strongPower G e0))
    (Z1 : Realisation Letter Letter.sep (SimpleGraph.strongPower G k1))
    (Z2 : Realisation Letter Letter.sep (SimpleGraph.strongPower G k2))
    (sX s1 s2 : Sizes) (hX : ∀ b, X.w b = sX.get b) (h1 : ∀ b, Z1.w b = s1.get b)
    (h2 : ∀ b, Z2.w b = s2.get b) :
    ∀ n a, (tailIter S X Z1 Z2 n).w a = (tailW S sX s1 s2 n).get a := by
  intro n
  induction n with
  | zero =>
    intro a
    rw [tailIter, w_castR, tailW]
    exact hX a
  | succ n ih =>
    intro a
    rw [tailIter, w_castR, tailW]
    exact w_node3 S _ _ s1 s2 ih h1 h2 a

end DagTail
end ShannonBounds.ExplorationC13FrontierR03
