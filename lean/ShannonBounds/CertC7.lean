/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.PortRealisation
import ShannonBounds.Layered
import ShannonBounds.Reindex
import ShannonBounds.Substitutions
import ShannonBounds.TerminalCodes

set_option maxRecDepth 4000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 4000
set_option exponentiation.threshold 20000

/-!
# `Theta (C7) >= 3.258827985920007`, mixing both orientations of the base

The schedule uses the base realisation `w` and its reindexing `sigma w` -- see
`ShannonBounds/Reindex.lean` -- as *different children of the same node*:

```
n3  = Sa (w, w, w)          q2  = Sb (w, sigma w)
n5  = Sa (n3, w, w)         n4  = Sa (q2, w, w)
n6  = Sa (n3, w, q2)        n8  = Sa (n4, q2, q2)
n11 = Sa (n5, n3, n3)       n25 = Sc  (n6, n11, n8)
```

with the `49`-word terminal code `K` on four copies of `n25`, so `E = 100`.  The
base lives in `C7^(box 5)`, hence `C7^(box 500)`.

`sigma w` is a realisation *in the same graph* as `w`, so a single node may take both as
children; `q2` is that node.

The base weights are `(B,N,A,D,O,H,V) = (359,322,19,26,8,8,8)`, so the flip exchanges the two
footprint sizes `19` and `26`; the remaining five entries are fixed by `sigma`.
-/

namespace ShannonBounds
namespace CertC7

open SimpleGraph

/-- An arity-`3` substitution. -/
abbrev Sa : Subst Letter Letter.sep 3 := Substitutions.S3a

/-- An arity-`2` substitution. -/
abbrev Sb : Subst Letter Letter.sep 2 := Substitutions.S2a

/-- An arity-`3` substitution. -/
abbrev Sc : Subst Letter Letter.sep 3 := Substitutions.S3b

/-- The terminal code, of `49` words of length `4`. -/
abbrev K : Code Letter Letter.sep 4 := TerminalCodes.K4a

/-- The size of each of the seven families of the base port system. -/
def w0 : Letter → Nat
  | .B => 359
  | .N => 322
  | .A => 19
  | .D => 26
  | .O => 8
  | .H => 8
  | .V => 8

/-- The same sizes after reindexing by `sigma`: `A` and `D` are exchanged. -/
def w0f : Letter → Nat
  | .B => 359
  | .N => 322
  | .A => 26
  | .D => 19
  | .O => 8
  | .H => 8
  | .V => 8

/-- The size of the independent set the construction produces. -/
def M : Nat :=
  33940530657597882925191574865912775290145601934564455387323703442021579944400980807795193611076112075323881909090940058499574128346740787309714999247400230617883682426438549034212777014725965605971521485006367332005696041071231504616529306366222412425335489

variable {α : Type*} [Fintype α] [DecidableEq α]
  {G : SimpleGraph α} [DecidableRel G.Adj]

/-- The base realisation, seen in the first strong power. -/
def R1 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 1) :=
  R.mapIso (strongPower_one_iso G).symm

lemma w_R1 (R : Realisation Letter Letter.sep G) (a : Letter) :
    (R1 R).w a = R.w a := by simp [R1]

/-- The base realisation reindexed by `sigma`, in the same graph. -/
def Rf (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 1) :=
  (R1 R).reindex Letter.sigma Letter.sigma_sep

lemma w_Rf (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) (b : Letter) :
    (Rf R).w b = w0f b := by
  have e : (Rf R).w b = R.w (Letter.sigma b) := by
    rw [Rf, Realisation.w_reindex, w_R1]
  rw [e, h]
  cases b <;> rfl

/-! ### Node `n3`, exponent `3` -/

/-- The child exponents of node `n3`. -/
def en3 : Fin 3 → Nat := Fin.cases 1 (Fin.cases 1 (fun _ => 1))

/-- The children of node `n3`. -/
def chn3 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (en3 i)) :=
  Fin.cases (R1 R) (Fin.cases (R1 R) (fun _ => (R1 R)))

/-- Node `n3`. -/
def Rn3 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 3) :=
  Realisation.multiSubst en3 (chn3 R) Sa

/-- The seven sizes at node `n3`. -/
def wn3 : Letter → Nat
  | .B => 46990439
  | .N => 35342398
  | .A => 5948463
  | .D => 8140002
  | .O => 16200
  | .H => 2504616
  | .V => 2504616

/-- Node `n3` has the sizes `wn3`. -/
lemma stepn3 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rn3 R).w a = wn3 a := by
  intro a
  change (Realisation.multiSubst en3 (chn3 R) Sa).w a = wn3 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chn3 R 0).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h1 : ∀ b, (chn3 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h2 : ∀ b, (chn3 R 2).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `q2`, exponent `2` -/

/-- The child exponents of node `q2`. -/
def eq2 : Fin 2 → Nat := Fin.cases 1 (fun _ => 1)

/-- The children of node `q2`. -/
def chq2 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eq2 i)) :=
  Fin.cases (R1 R) (fun _ => (Rf R))

/-- Node `q2`. -/
def Rq2 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 2) :=
  Realisation.multiSubst eq2 (chq2 R) Sb

/-- The seven sizes at node `q2`. -/
def wq2 : Letter → Nat
  | .B => 129601
  | .N => 105709
  | .A => 12236
  | .D => 16744
  | .O => 5152
  | .H => 5152
  | .V => 5152

/-- Node `q2` has the sizes `wq2`. -/
lemma stepq2 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rq2 R).w a = wq2 a := by
  intro a
  change (Realisation.multiSubst eq2 (chq2 R) Sb).w a = wq2 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chq2 R 0).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h1 : ∀ b, (chq2 R 1).w b = w0f b := fun b => w_Rf R h b
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `n5`, exponent `5` -/

/-- The child exponents of node `n5`. -/
def en5 : Fin 3 → Nat := Fin.cases 3 (Fin.cases 1 (fun _ => 1))

/-- The children of node `n5`. -/
def chn5 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (en5 i)) :=
  Fin.cases (Rn3 R) (Fin.cases (R1 R) (fun _ => (R1 R)))

/-- Node `n5`. -/
def Rn5 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 5) :=
  Realisation.multiSubst en5 (chn5 R) Sa

/-- The seven sizes at node `n5`. -/
def wn5 : Letter → Nat
  | .B => 6235175428199
  | .N => 4144293265882
  | .A => 1061255657195
  | .D => 1452244583530
  | .O => 32805000
  | .H => 446844487240
  | .V => 446844487240

/-- Node `n5` has the sizes `wn5`. -/
lemma stepn5 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rn5 R).w a = wn5 a := by
  intro a
  change (Realisation.multiSubst en5 (chn5 R) Sa).w a = wn5 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chn5 R 0).w b = wn3 b := fun b => stepn3 R h b
  have h1 : ∀ b, (chn5 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h2 : ∀ b, (chn5 R 2).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `n4`, exponent `4` -/

/-- The child exponents of node `n4`. -/
def en4 : Fin 3 → Nat := Fin.cases 2 (Fin.cases 1 (fun _ => 1))

/-- The children of node `n4`. -/
def chn4 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (en4 i)) :=
  Fin.cases (Rq2 R) (Fin.cases (R1 R) (fun _ => (R1 R)))

/-- Node `n4`. -/
def Rn4 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 4) :=
  Realisation.multiSubst en4 (chn4 R) Sa

/-- The seven sizes at node `n4`. -/
def wn4 : Letter → Nat
  | .B => 17095029121
  | .N => 12014233081
  | .A => 2586910648
  | .D => 3539982992
  | .O => 10432800
  | .H => 1089225536
  | .V => 1089225536

/-- Node `n4` has the sizes `wn4`. -/
lemma stepn4 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rn4 R).w a = wn4 a := by
  intro a
  change (Realisation.multiSubst en4 (chn4 R) Sa).w a = wn4 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chn4 R 0).w b = wq2 b := fun b => stepq2 R h b
  have h1 : ∀ b, (chn4 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h2 : ∀ b, (chn4 R 2).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `n6`, exponent `6` -/

/-- The child exponents of node `n6`. -/
def en6 : Fin 3 → Nat := Fin.cases 3 (Fin.cases 1 (fun _ => 2))

/-- The children of node `n6`. -/
def chn6 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (en6 i)) :=
  Fin.cases (Rn3 R) (Fin.cases (R1 R) (fun _ => (Rq2 R)))

/-- Node `n6`. -/
def Rn6 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 6) :=
  Realisation.multiSubst en6 (chn6 R) Sa

/-- The seven sizes at node `n6`. -/
def wn6 : Letter → Nat
  | .B => 2278673747121601
  | .N => 1447569942446629
  | .A => 420465893668548
  | .D => 575374380809592
  | .O => 21126420000
  | .H => 177038271018336
  | .V => 177038271018336

/-- Node `n6` has the sizes `wn6`. -/
lemma stepn6 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rn6 R).w a = wn6 a := by
  intro a
  change (Realisation.multiSubst en6 (chn6 R) Sa).w a = wn6 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chn6 R 0).w b = wn3 b := fun b => stepn3 R h b
  have h1 : ∀ b, (chn6 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h2 : ∀ b, (chn6 R 2).w b = wq2 b := fun b => stepq2 R h b
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `n8`, exponent `8` -/

/-- The child exponents of node `n8`. -/
def en8 : Fin 3 → Nat := Fin.cases 4 (Fin.cases 2 (fun _ => 2))

/-- The children of node `n8`. -/
def chn8 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (en8 i)) :=
  Fin.cases (Rn4 R) (Fin.cases (Rq2 R) (fun _ => (Rq2 R)))

/-- Node `n8`. -/
def Rn8 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 8) :=
  Realisation.multiSubst en8 (chn8 R) Sa

/-- The seven sizes at node `n8`. -/
def wn8 : Letter → Nat
  | .B => 305587158665926014721
  | .N => 181880622200467202161
  | .A => 62159494969585492976
  | .D => 85060361537327516704
  | .O => 8761886925120000
  | .H => 26172418934562312832
  | .V => 26172418934562312832

/-- Node `n8` has the sizes `wn8`. -/
lemma stepn8 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rn8 R).w a = wn8 a := by
  intro a
  change (Realisation.multiSubst en8 (chn8 R) Sa).w a = wn8 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chn8 R 0).w b = wn4 b := fun b => stepn4 R h b
  have h1 : ∀ b, (chn8 R 1).w b = wq2 b := fun b => stepq2 R h b
  have h2 : ∀ b, (chn8 R 2).w b = wq2 b := fun b => stepq2 R h b
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `n11`, exponent `11` -/

/-- The child exponents of node `n11`. -/
def en11 : Fin 3 → Nat := Fin.cases 5 (Fin.cases 3 (fun _ => 3))

/-- The children of node `n11`. -/
def chn11 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (en11 i)) :=
  Fin.cases (Rn5 R) (Fin.cases (Rn3 R) (fun _ => (Rn3 R)))

/-- Node `n11`. -/
def Rn11 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 11) :=
  Realisation.multiSubst en11 (chn11 R) Sa

/-- The seven sizes at node `n11`. -/
def wn11 : Letter → Nat
  | .B => 15097902030578999012675293799
  | .N => 8502199133999213839641863278
  | .A => 3278775762270546122552224991
  | .D => 4486745779949168378229360514
  | .O => 6511295374874461125000
  | .H => 1380537163061282577916726312
  | .V => 1380537163061282577916726312

/-- Node `n11` has the sizes `wn11`. -/
lemma stepn11 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rn11 R).w a = wn11 a := by
  intro a
  change (Realisation.multiSubst en11 (chn11 R) Sa).w a = wn11 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chn11 R 0).w b = wn5 b := fun b => stepn5 R h b
  have h1 : ∀ b, (chn11 R 1).w b = wn3 b := fun b => stepn3 R h b
  have h2 : ∀ b, (chn11 R 2).w b = wn3 b := fun b => stepn3 R h b
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `n25`, exponent `25` -/

/-- The child exponents of node `n25`. -/
def en25 : Fin 3 → Nat := Fin.cases 6 (Fin.cases 11 (fun _ => 8))

/-- The children of node `n25`. -/
def chn25 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (en25 i)) :=
  Fin.cases (Rn6 R) (Fin.cases (Rn11 R) (fun _ => (Rn8 R)))

/-- Node `n25`. -/
def Rn25 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 25) :=
  Realisation.multiSubst en25 (chn25 R) Sc

/-- The seven sizes at node `n25`. -/
def wn25 : Letter → Nat
  | .B => 12593797505315299225610769552556855043535417619319645431747882343
  | .N => 3239680130385807376586939112980318460438029786472282495555948646
  | .A => 4233842006627322862986852002998375367665576404790609666085147319
  | .D => 5793678535384757601982008004103039976805525606555571122011254226
  | .O => 0
  | .H => 965758516120747443667198160038073029584084964580560209646982024
  | .V => 965758516120747443667198160038073029584084964580560209646982024

/-- Node `n25` has the sizes `wn25`. -/
lemma stepn25 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rn25 R).w a = wn25 a := by
  intro a
  change (Realisation.multiSubst en25 (chn25 R) Sc).w a = wn25 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chn25 R 0).w b = wn6 b := fun b => stepn6 R h b
  have h1 : ∀ b, (chn25 R 1).w b = wn11 b := fun b => stepn11 R h b
  have h2 : ∀ b, (chn25 R 2).w b = wn8 b := fun b => stepn8 R h b
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### The bound -/

/-- The exponents of the four terminal children. -/
def eT : Fin 4 → Nat := Fin.cases 25 (Fin.cases 25 (Fin.cases 25 (fun _ => 25)))

/-- The four terminal children, all the same node. -/
def terminalChildren (R : Realisation Letter Letter.sep G) :
    (i : Fin 4) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eT i)) :=
  Fin.cases (Rn25 R) (Fin.cases (Rn25 R) (Fin.cases (Rn25 R) (fun _ => Rn25 R)))

/-- **The bound.**  A port system whose seven families have the sizes of `w0` gives an
independent set of size `M` in `G^(box 100)`. -/
theorem bound (S : RichPortSystem G) (hw : ∀ a, (S.fam a).card = w0 a) :
    M ≤ (SimpleGraph.strongPower G 100).indepNum := by
  have base_w : ∀ a, S.toRealisation.w a = w0 a := hw
  refine le_trans (le_of_eq ?_) (le_indepNum_multiCode eT (terminalChildren S.toRealisation) K)
  have h0 : ∀ a, (terminalChildren S.toRealisation 0).w a = wn25 a := by
    intro a; change (Rn25 S.toRealisation).w a = wn25 a; exact stepn25 S.toRealisation base_w a
  have h1 : ∀ a, (terminalChildren S.toRealisation 1).w a = wn25 a := by
    intro a; change (Rn25 S.toRealisation).w a = wn25 a; exact stepn25 S.toRealisation base_w a
  have h2 : ∀ a, (terminalChildren S.toRealisation 2).w a = wn25 a := by
    intro a; change (Rn25 S.toRealisation).w a = wn25 a; exact stepn25 S.toRealisation base_w a
  have h3 : ∀ a, (terminalChildren S.toRealisation 3).w a = wn25 a := by
    intro a; change (Rn25 S.toRealisation).w a = wn25 a; exact stepn25 S.toRealisation base_w a
  simp only [Fin.prod_univ_four, h0, h1, h2, h3]
  native_decide

end CertC7
end ShannonBounds
