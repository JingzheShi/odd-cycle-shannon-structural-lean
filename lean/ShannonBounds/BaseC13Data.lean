/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# Base data for `C13^(box 6)`: a `K`-equivariant certificate

`alpha(C13^6) >= 62530`; the base set `I` lives in `Fin 4826809 = Fin (13^6)`.

The construction goes back to the cube construction of Baumert, McEliece, Rodemich,
Rumsey, Stanley and Taylor.  See the paper.

## The base is a blow-up

All four objects of the rich port system -- the independent set `I`, the auxiliary set
`X`, and the two transversals `P_0` (parents) and `P_1` (alternatives) -- are invariant
under translation by the rank-2 subgroup

    K = < (1,2,0,0,0,1), (0,0,1,11,0,0) >  <=  Z_13^6,   |K| = 169,

and `K` is *exactly* the kernel of the syndrome map

    sigma(w) = ( w1 - 2 w0, w3 - 11 w2, w4, w5 - w0 )  mod 13   in Z_13^4

(`syn` below; `w0` is the leading base-13 digit).  So each of the four objects is a union
of full `sigma`-fibres, and the certificate is a list of fibres:

    I   = sigma^{-1}(S),    |S|  = 370      X   = sigma^{-1}(S_X),  |S_X| = 370
    P_0 = sigma^{-1}(S_P),  |S_P| = 6       P_1 = sigma^{-1}(S_A),  |S_A| = 6

with `|K| = 169` and `169 * 370 = 62530`, `169 * 6 = 1014`.

## Checking on orbit representatives

Conflict in the strong power is *translation invariant*: `wconfN (u+t) (v+t) = wconfN u v`
(`wconfN_tadd`).  Since every object above is `K`-invariant and `K` acts by translation,
the whole rich-port-system predicate is `K`-equivariant, and a property of a port -- being
in `I`, having a private alternative, hitting a given footprint class -- is checked on
**one representative per `K`-orbit**: six ports and six alternatives.

## The soundness condition

`ker_meet_offsets_empty` -- **`K` meets no nonzero offset**: no nonzero `d` in
`{-1,0,1}^6` has `sigma(d) = 0`.  Equivalently (`syn_ne_of_conflict_of_ne`) *distinct
conflicting words never share a syndrome*, i.e. every `K`-orbit is itself an independent
set of `C13^(box 6)`.  This is what makes the descent sound.

`delta_card` proves `Delta.length = 482`; distinct offsets may share a syndrome.
-/
import ShannonBounds.Lift

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

namespace ShannonBounds
namespace BaseC13

/-- Words of `C13^6`, encoded in base 13. -/
abbrev Code := Fin 4826809

/-! ### The coordinate conflict test -/

def sconfSpec (a b : Nat) : Bool :=
  ((a + 13 - b) % 13 == 0) || ((a + 13 - b) % 13 == 1) || ((a + 13 - b) % 13 == 12)

def sconf (a b : Nat) : Bool := (a + 14 - b) % 13 <= 2

theorem sconf_eq_spec : ∀ a < 13, ∀ b < 13, sconf a b = sconfSpec a b := by native_decide
theorem sconf_symm : ∀ a < 13, ∀ b < 13, sconf a b = sconf b a := by native_decide
theorem sconf_refl : ∀ a < 13, sconf a a = true := by native_decide

/-- **Translation invariance, one coordinate at a time.**  Shifting both arguments by the
same residue does not change the cyclic conflict test.  This is the seed of the whole
`K`-equivariance argument. -/
theorem sconf_shift : ∀ a < 13, ∀ b < 13, ∀ s < 13,
    sconf ((a + s) % 13) ((b + s) % 13) = sconf a b := by native_decide

/-- The three admissible cyclic offsets, as residues mod 13. -/
def ds : List Nat := [12, 0, 1]

theorem sconf_cases : ∀ a < 13, ∀ b < 13,
    sconf a b = true → ds.any (fun i => b == (a + i) % 13) = true := by native_decide

/-! ### Conflict in `C13^(box 6)` -/

def wconfN (u v : Nat) : Bool :=
  sconf (u / 1 % 13) (v / 1 % 13) && sconf (u / 13 % 13) (v / 13 % 13) &&
    sconf (u / 169 % 13) (v / 169 % 13) && sconf (u / 2197 % 13) (v / 2197 % 13) &&
    sconf (u / 28561 % 13) (v / 28561 % 13) && sconf (u / 371293 % 13) (v / 371293 % 13)

def dgt (m : Nat) (u : Code) : Nat := u.val / m % 13

lemma dgt_lt (m : Nat) (u : Code) : dgt m u < 13 := Nat.mod_lt _ (by decide)

def wconf (u v : Code) : Bool := wconfN u.val v.val

lemma wconf_eq (u v : Code) :
    wconf u v = (sconf (dgt 1 u) (dgt 1 v) && sconf (dgt 13 u) (dgt 13 v) &&
      sconf (dgt 169 u) (dgt 169 v) && sconf (dgt 2197 u) (dgt 2197 v) &&
      sconf (dgt 28561 u) (dgt 28561 v) && sconf (dgt 371293 u) (dgt 371293 v)) := rfl

theorem wconfN_symm (u v : Nat) : wconfN u v = wconfN v u := by
  have h : ∀ m : Nat, sconf (u / m % 13) (v / m % 13) = sconf (v / m % 13) (u / m % 13) :=
    fun m => sconf_symm _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))
  simp only [wconfN, h]

lemma wconf_symm (u v : Code) : wconf u v = wconf v u := wconfN_symm u.val v.val

theorem wconfN_refl (u : Nat) : wconfN u u = true := by
  have h : ∀ m : Nat, sconf (u / m % 13) (u / m % 13) = true :=
    fun m => sconf_refl _ (Nat.mod_lt _ (by decide))
  simp only [wconfN, h]
  rfl

lemma wconf_refl (u : Code) : wconf u u = true := wconfN_refl u.val

/-- `C13^(box 6)`. -/
def G6 : SimpleGraph Code where
  Adj u v := u ≠ v ∧ wconf u v = true
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by rw [wconf_symm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance decG6 : DecidableRel G6.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ wconf u v = true))

lemma conflict_G6 (u v : Code) : conflict G6 u v ↔ wconf u v = true := by
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · exact wconf_refl u
    · exact h
  · intro h
    by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr ⟨huv, h⟩

/-! ### Digit reconstruction and the translation action

`mk6` assembles six base-13 digits into a word; `tadd` and `tsub` are coordinatewise
addition and subtraction mod 13, i.e. the translation action of `Z_13^6` on itself. -/

def mk6 (a b c d e f : Nat) : Nat := (((((a * 13 + b) * 13 + c) * 13 + d) * 13 + e) * 13 + f)

theorem recon6 (v : Nat) (h : v < 4826809) :
    mk6 (v / 371293 % 13) (v / 28561 % 13) (v / 2197 % 13) (v / 169 % 13)
      (v / 13 % 13) (v / 1 % 13) = v := by
  unfold mk6; omega

theorem mk6_lt {a b c d e f : Nat} (ha : a < 13) (hb : b < 13) (hc : c < 13) (hd : d < 13) (he : e < 13)
    (hf : f < 13) : mk6 a b c d e f < 4826809 := by unfold mk6; omega

theorem mk6_5 {a b c d e f : Nat} (ha : a < 13) (hb : b < 13) (hc : c < 13) (hd : d < 13) (he : e < 13)
    (hf : f < 13) : mk6 a b c d e f / 371293 % 13 = a := by unfold mk6; omega

theorem mk6_4 {a b c d e f : Nat} (_ha : a < 13) (hb : b < 13) (hc : c < 13) (hd : d < 13) (he : e < 13)
    (hf : f < 13) : mk6 a b c d e f / 28561 % 13 = b := by unfold mk6; omega

theorem mk6_3 {a b c d e f : Nat} (_ha : a < 13) (_hb : b < 13) (hc : c < 13) (hd : d < 13) (he : e < 13)
    (hf : f < 13) : mk6 a b c d e f / 2197 % 13 = c := by unfold mk6; omega

theorem mk6_2 {a b c d e f : Nat} (_ha : a < 13) (_hb : b < 13) (_hc : c < 13) (hd : d < 13) (he : e < 13)
    (hf : f < 13) : mk6 a b c d e f / 169 % 13 = d := by unfold mk6; omega

theorem mk6_1 {a b c d e f : Nat} (_ha : a < 13) (_hb : b < 13) (_hc : c < 13) (_hd : d < 13) (he : e < 13)
    (hf : f < 13) : mk6 a b c d e f / 13 % 13 = e := by unfold mk6; omega

theorem mk6_0 {a b c d e f : Nat} (_ha : a < 13) (_hb : b < 13) (_hc : c < 13) (_hd : d < 13) (_he : e < 13)
    (hf : f < 13) : mk6 a b c d e f / 1 % 13 = f := by unfold mk6; omega

/-- coordinatewise addition mod 13: the translation action of `Z_13^6` -/
def tadd (u t : Nat) : Nat :=
  mk6 ((u / 371293 % 13 + t / 371293 % 13) % 13) ((u / 28561 % 13 + t / 28561 % 13) % 13)
      ((u / 2197 % 13 + t / 2197 % 13) % 13) ((u / 169 % 13 + t / 169 % 13) % 13)
      ((u / 13 % 13 + t / 13 % 13) % 13) ((u / 1 % 13 + t / 1 % 13) % 13)

/-- coordinatewise subtraction mod 13 -/
def tsub (u t : Nat) : Nat :=
  mk6 ((u / 371293 % 13 + 13 - t / 371293 % 13) % 13)
      ((u / 28561 % 13 + 13 - t / 28561 % 13) % 13)
      ((u / 2197 % 13 + 13 - t / 2197 % 13) % 13)
      ((u / 169 % 13 + 13 - t / 169 % 13) % 13)
      ((u / 13 % 13 + 13 - t / 13 % 13) % 13)
      ((u / 1 % 13 + 13 - t / 1 % 13) % 13)

private theorem ml (x : Nat) : x % 13 < 13 := Nat.mod_lt _ (by decide)

theorem tadd_lt (u t : Nat) : tadd u t < 4826809 :=
  mk6_lt (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)

theorem tsub_lt (u t : Nat) : tsub u t < 4826809 :=
  mk6_lt (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)

theorem tadd_5 (u t : Nat) : tadd u t / 371293 % 13 = (u / 371293 % 13 + t / 371293 % 13) % 13 :=
  mk6_5 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)
theorem tadd_4 (u t : Nat) : tadd u t / 28561 % 13 = (u / 28561 % 13 + t / 28561 % 13) % 13 :=
  mk6_4 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)
theorem tadd_3 (u t : Nat) : tadd u t / 2197 % 13 = (u / 2197 % 13 + t / 2197 % 13) % 13 :=
  mk6_3 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)
theorem tadd_2 (u t : Nat) : tadd u t / 169 % 13 = (u / 169 % 13 + t / 169 % 13) % 13 :=
  mk6_2 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)
theorem tadd_1 (u t : Nat) : tadd u t / 13 % 13 = (u / 13 % 13 + t / 13 % 13) % 13 :=
  mk6_1 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)
theorem tadd_0 (u t : Nat) : tadd u t / 1 % 13 = (u / 1 % 13 + t / 1 % 13) % 13 :=
  mk6_0 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)

theorem tsub_5 (u t : Nat) :
    tsub u t / 371293 % 13 = (u / 371293 % 13 + 13 - t / 371293 % 13) % 13 :=
  mk6_5 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)
theorem tsub_4 (u t : Nat) :
    tsub u t / 28561 % 13 = (u / 28561 % 13 + 13 - t / 28561 % 13) % 13 :=
  mk6_4 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)
theorem tsub_3 (u t : Nat) :
    tsub u t / 2197 % 13 = (u / 2197 % 13 + 13 - t / 2197 % 13) % 13 :=
  mk6_3 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)
theorem tsub_2 (u t : Nat) :
    tsub u t / 169 % 13 = (u / 169 % 13 + 13 - t / 169 % 13) % 13 :=
  mk6_2 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)
theorem tsub_1 (u t : Nat) : tsub u t / 13 % 13 = (u / 13 % 13 + 13 - t / 13 % 13) % 13 :=
  mk6_1 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)
theorem tsub_0 (u t : Nat) : tsub u t / 1 % 13 = (u / 1 % 13 + 13 - t / 1 % 13) % 13 :=
  mk6_0 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)

/-- Two words with the same six base-13 digits are equal. -/
theorem eq_of_digits {x y : Nat} (hx : x < 4826809) (hy : y < 4826809)
    (h5 : x / 371293 % 13 = y / 371293 % 13) (h4 : x / 28561 % 13 = y / 28561 % 13)
    (h3 : x / 2197 % 13 = y / 2197 % 13) (h2 : x / 169 % 13 = y / 169 % 13)
    (h1 : x / 13 % 13 = y / 13 % 13) (h0 : x / 1 % 13 = y / 1 % 13) : x = y := by
  rw [← recon6 x hx, ← recon6 y hy, h5, h4, h3, h2, h1, h0]

private theorem cancel13 {x y z : Nat} (h : (x % 13 + z) % 13 = (y % 13 + z) % 13) :
    x % 13 = y % 13 := by omega

theorem tadd_zero (u : Nat) (hu : u < 4826809) : tadd u 0 = u :=
  eq_of_digits (tadd_lt _ _) hu
    (by simp only [tadd_5]; omega) (by simp only [tadd_4]; omega)
    (by simp only [tadd_3]; omega) (by simp only [tadd_2]; omega)
    (by simp only [tadd_1]; omega) (by simp only [tadd_0]; omega)

/-- **`v = u + (v - u)`.**  Two words are always related by a translation. -/
theorem tadd_tsub (u v : Nat) (hu : u < 4826809) : tadd v (tsub u v) = u :=
  eq_of_digits (tadd_lt _ _) hu
    (by simp only [tadd_5, tsub_5]; omega) (by simp only [tadd_4, tsub_4]; omega)
    (by simp only [tadd_3, tsub_3]; omega) (by simp only [tadd_2, tsub_2]; omega)
    (by simp only [tadd_1, tsub_1]; omega) (by simp only [tadd_0, tsub_0]; omega)

/-- Translation is injective. -/
theorem tadd_cancel {u v t : Nat} (hu : u < 4826809) (hv : v < 4826809)
    (h : tadd u t = tadd v t) : u = v := by
  have e5 := congrArg (fun x => x / 371293 % 13) h
  have e4 := congrArg (fun x => x / 28561 % 13) h
  have e3 := congrArg (fun x => x / 2197 % 13) h
  have e2 := congrArg (fun x => x / 169 % 13) h
  have e1 := congrArg (fun x => x / 13 % 13) h
  have e0 := congrArg (fun x => x / 1 % 13) h
  simp only [tadd_5] at e5
  simp only [tadd_4] at e4
  simp only [tadd_3] at e3
  simp only [tadd_2] at e2
  simp only [tadd_1] at e1
  simp only [tadd_0] at e0
  exact eq_of_digits hu hv (cancel13 e5) (cancel13 e4) (cancel13 e3) (cancel13 e2)
    (cancel13 e1) (cancel13 e0)

theorem tadd_comm (u t : Nat) : tadd u t = tadd t u :=
  eq_of_digits (tadd_lt _ _) (tadd_lt _ _)
    (by simp only [tadd_5]; omega) (by simp only [tadd_4]; omega)
    (by simp only [tadd_3]; omega) (by simp only [tadd_2]; omega)
    (by simp only [tadd_1]; omega) (by simp only [tadd_0]; omega)

theorem tadd_swap (x y t : Nat) : tadd (tadd x t) y = tadd (tadd x y) t :=
  eq_of_digits (tadd_lt _ _) (tadd_lt _ _)
    (by simp only [tadd_5]; omega) (by simp only [tadd_4]; omega)
    (by simp only [tadd_3]; omega) (by simp only [tadd_2]; omega)
    (by simp only [tadd_1]; omega) (by simp only [tadd_0]; omega)

/-- **Conflict is translation invariant.**  The whole `K`-descent rests on this line. -/
theorem wconfN_tadd (u v t : Nat) : wconfN (tadd u t) (tadd v t) = wconfN u v := by
  simp only [wconfN, tadd_0, tadd_1, tadd_2, tadd_3, tadd_4, tadd_5]
  rw [sconf_shift (u / 1 % 13) (ml _) (v / 1 % 13) (ml _) (t / 1 % 13) (ml _),
    sconf_shift (u / 13 % 13) (ml _) (v / 13 % 13) (ml _) (t / 13 % 13) (ml _),
    sconf_shift (u / 169 % 13) (ml _) (v / 169 % 13) (ml _) (t / 169 % 13) (ml _),
    sconf_shift (u / 2197 % 13) (ml _) (v / 2197 % 13) (ml _) (t / 2197 % 13) (ml _),
    sconf_shift (u / 28561 % 13) (ml _) (v / 28561 % 13) (ml _) (t / 28561 % 13) (ml _),
    sconf_shift (u / 371293 % 13) (ml _) (v / 371293 % 13) (ml _) (t / 371293 % 13) (ml _)]

/-! ### The syndrome -/

def packS (p q r s : Nat) : Nat := ((p * 13 + q) * 13 + r) * 13 + s

theorem packS_0 {p q r s : Nat} (hp : p < 13) (hq : q < 13) (hr : r < 13) (hs : s < 13) :
    packS p q r s / 2197 % 13 = p := by unfold packS; omega

theorem packS_1 {p q r s : Nat} (_hp : p < 13) (hq : q < 13) (hr : r < 13) (hs : s < 13) :
    packS p q r s / 169 % 13 = q := by unfold packS; omega

theorem packS_2 {p q r s : Nat} (_hp : p < 13) (_hq : q < 13) (hr : r < 13) (hs : s < 13) :
    packS p q r s / 13 % 13 = r := by unfold packS; omega

theorem packS_3 {p q r s : Nat} (_hp : p < 13) (_hq : q < 13) (_hr : r < 13) (hs : s < 13) :
    packS p q r s % 13 = s := by unfold packS; omega

theorem packS_lt {p q r s : Nat} (hp : p < 13) (hq : q < 13) (hr : r < 13) (hs : s < 13) :
    packS p q r s < 28561 := by unfold packS; omega

/-- `sigma(w) = (w1 - 2 w0, w3 - 11 w2, w4, w5 - w0)`, with `-2 = 11`, `-11 = 2`,
`-1 = 12` as nonnegative representatives. -/
def synD (a b c d e f : Nat) : Nat :=
  packS ((b + 11 * a) % 13) ((d + 2 * c) % 13) (e % 13) ((f + 12 * a) % 13)

def syn (u : Nat) : Nat :=
  synD (u / 371293 % 13) (u / 28561 % 13) (u / 2197 % 13) (u / 169 % 13)
    (u / 13 % 13) (u / 1 % 13)

theorem syn_lt (u : Nat) : syn u < 28561 := by
  unfold syn synD
  exact packS_lt (ml _) (ml _) (ml _) (ml _)

/-- componentwise addition of syndrome codes -/
def addSyn (s e : Nat) : Nat :=
  packS ((s / 2197 % 13 + e / 2197 % 13) % 13) ((s / 169 % 13 + e / 169 % 13) % 13)
    ((s / 13 % 13 + e / 13 % 13) % 13) ((s % 13 + e % 13) % 13)

theorem comp0 (a b i j : Nat) :
    ((b + j) % 13 + 11 * ((a + i) % 13)) % 13
      = ((b + 11 * a) % 13 + (j + 11 * i) % 13) % 13 := by omega

theorem comp1 (c d k l : Nat) :
    ((d + l) % 13 + 2 * ((c + k) % 13)) % 13
      = ((d + 2 * c) % 13 + (l + 2 * k) % 13) % 13 := by omega

theorem comp2 (e m : Nat) : ((e + m) % 13) % 13 = (e % 13 + m % 13) % 13 := by omega

theorem comp3 (a f i n : Nat) :
    ((f + n) % 13 + 12 * ((a + i) % 13)) % 13
      = ((f + 12 * a) % 13 + (n + 12 * i) % 13) % 13 := by omega

/-- **The bridge: `sigma` is additive.**  Translating a word by an offset translates
its syndrome by the offset's syndrome. -/
theorem synD_add (a b c d e f i j k l m n : Nat) :
    synD ((a + i) % 13) ((b + j) % 13) ((c + k) % 13) ((d + l) % 13)
        ((e + m) % 13) ((f + n) % 13)
      = addSyn (synD a b c d e f) (synD i j k l m n) := by
  unfold addSyn synD
  rw [packS_0 (by omega) (by omega) (by omega) (by omega),
      packS_1 (by omega) (by omega) (by omega) (by omega),
      packS_2 (by omega) (by omega) (by omega) (by omega),
      packS_3 (by omega) (by omega) (by omega) (by omega),
      packS_0 (by omega) (by omega) (by omega) (by omega),
      packS_1 (by omega) (by omega) (by omega) (by omega),
      packS_2 (by omega) (by omega) (by omega) (by omega),
      packS_3 (by omega) (by omega) (by omega) (by omega)]
  rw [comp0, comp1, comp2, comp3]

/-- **`sigma` intertwines translation with syndrome addition.** -/
theorem syn_tadd (u t : Nat) : syn (tadd u t) = addSyn (syn u) (syn t) := by
  show synD (tadd u t / 371293 % 13) (tadd u t / 28561 % 13) (tadd u t / 2197 % 13)
      (tadd u t / 169 % 13) (tadd u t / 13 % 13) (tadd u t / 1 % 13) = _
  rw [tadd_5 u t, tadd_4 u t, tadd_3 u t, tadd_2 u t, tadd_1 u t, tadd_0 u t]
  exact synD_add _ _ _ _ _ _ _ _ _ _ _ _

theorem addSyn_zero {s : Nat} (hs : s < 28561) : addSyn s 0 = s := by unfold addSyn packS; omega

theorem addSyn_cancel {x e : Nat} (_hx : x < 28561) (he : e < 28561)
    (h : addSyn x e = x) : e = 0 := by
  have e0 := congrArg (fun y => y / 2197 % 13) h
  have e1 := congrArg (fun y => y / 169 % 13) h
  have e2 := congrArg (fun y => y / 13 % 13) h
  have e3 := congrArg (fun y => y % 13) h
  simp only [addSyn, packS_0 (ml _) (ml _) (ml _) (ml _), packS_1 (ml _) (ml _) (ml _) (ml _),
    packS_2 (ml _) (ml _) (ml _) (ml _), packS_3 (ml _) (ml _) (ml _) (ml _)] at e0 e1 e2 e3
  omega

/-- Translating by an element of `K = ker sigma` does not move the syndrome. -/
theorem syn_tadd_ker {u t : Nat} (ht : syn t = 0) : syn (tadd u t) = syn u := by
  rw [syn_tadd, ht, addSyn_zero (syn_lt u)]

/-- **The `K`-orbit of a word is exactly its `sigma`-fibre.**  Two words with the same
syndrome differ by a translation lying in `K = ker sigma`.  Both inclusions of this
statement are what let a `K`-invariant object be presented as a list of syndromes. -/
theorem exists_ker_shift {u v : Nat} (hu : u < 4826809)
    (h : syn u = syn v) : ∃ t, t < 4826809 ∧ syn t = 0 ∧ tadd v t = u := by
  refine ⟨tsub u v, tsub_lt _ _, ?_, tadd_tsub u v hu⟩
  have h1 : syn (tadd v (tsub u v)) = addSyn (syn v) (syn (tsub u v)) := syn_tadd v _
  rw [tadd_tsub u v hu, h] at h1
  exact addSyn_cancel (syn_lt v) (syn_lt _) h1.symm

/-! ### The fibre coordinates

`enc` and `(syn, kap)` are mutually inverse bijections
`Fin 4826809 <-> [0,28561) x [0,169)`.  Concretely: a syndrome `(p,q,r,t)` and a
`K`-coordinate `k = (w0, w2)` determine the word
`w = (w0, p + 2 w0, w2, q + 11 w2, r, t + w0)`. -/

def enc (s k : Nat) : Nat :=
  mk6 (k / 13 % 13)
      ((s / 2197 % 13 + 2 * (k / 13 % 13)) % 13)
      (k % 13)
      ((s / 169 % 13 + 11 * (k % 13)) % 13)
      (s / 13 % 13)
      ((s % 13 + k / 13 % 13) % 13)

def kap (u : Nat) : Nat := (u / 371293 % 13) * 13 + u / 2197 % 13

theorem enc_lt (s k : Nat) : enc s k < 4826809 :=
  mk6_lt (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)

theorem kap_lt (u : Nat) : kap u < 169 := by
  have h1 : u / 371293 % 13 < 13 := ml _
  have h2 : u / 2197 % 13 < 13 := ml _
  unfold kap; omega

theorem syn_enc {s : Nat} (hs : s < 28561) (k : Nat) : syn (enc s k) = s := by
  show synD (enc s k / 371293 % 13) (enc s k / 28561 % 13) (enc s k / 2197 % 13)
      (enc s k / 169 % 13) (enc s k / 13 % 13) (enc s k / 1 % 13) = s
  unfold enc
  rw [mk6_5 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _),
      mk6_4 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _),
      mk6_3 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _),
      mk6_2 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _),
      mk6_1 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _),
      mk6_0 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)]
  unfold synD
  have s0 : ∀ x w : Nat, ((x % 13 + 2 * w) % 13 + 11 * w) % 13 = x % 13 := by
    intro x w; omega
  have s1 : ∀ x w : Nat, ((x % 13 + 11 * w) % 13 + 2 * w) % 13 = x % 13 := by
    intro x w; omega
  have s2 : ∀ x : Nat, (x % 13) % 13 = x % 13 := by intro x; omega
  have s3 : ∀ x w : Nat, ((x % 13 + w) % 13 + 12 * w) % 13 = x % 13 := by
    intro x w; omega
  rw [s0, s1, s2, s3]
  unfold packS; omega

theorem kap_enc (s : Nat) {k : Nat} (hk : k < 169) : kap (enc s k) = k := by
  show (enc s k / 371293 % 13) * 13 + enc s k / 2197 % 13 = k
  unfold enc
  rw [mk6_5 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _),
      mk6_3 (ml _) (ml _) (ml _) (ml _) (ml _) (ml _)]
  omega

theorem enc_syn_kap {u : Nat} (hu : u < 4826809) : enc (syn u) (kap u) = u := by
  have hk5 : kap u / 13 % 13 = u / 371293 % 13 := by
    have h2 : u / 2197 % 13 < 13 := ml _
    have h1 : u / 371293 % 13 < 13 := ml _
    unfold kap; omega
  have hk3 : kap u % 13 = u / 2197 % 13 := by
    have h2 : u / 2197 % 13 < 13 := ml _
    unfold kap; omega
  have hs0 : syn u / 2197 % 13 = (u / 28561 % 13 + 11 * (u / 371293 % 13)) % 13 :=
    packS_0 (ml _) (ml _) (ml _) (ml _)
  have hs1 : syn u / 169 % 13 = (u / 169 % 13 + 2 * (u / 2197 % 13)) % 13 :=
    packS_1 (ml _) (ml _) (ml _) (ml _)
  have hs2 : syn u / 13 % 13 = u / 13 % 13 % 13 :=
    packS_2 (ml _) (ml _) (ml _) (ml _)
  have hs3 : syn u % 13 = (u / 1 % 13 + 12 * (u / 371293 % 13)) % 13 :=
    packS_3 (ml _) (ml _) (ml _) (ml _)
  have g0 : ∀ x w : Nat, ((x % 13 + 11 * w) % 13 + 2 * w) % 13 = x % 13 := by
    intro x w; omega
  have g1 : ∀ x w : Nat, ((x % 13 + 2 * w) % 13 + 11 * w) % 13 = x % 13 := by
    intro x w; omega
  have g2 : ∀ x : Nat, x % 13 % 13 = x % 13 := by intro x; omega
  have g3 : ∀ x w : Nat, ((x % 13 + 12 * w) % 13 + w) % 13 = x % 13 := by
    intro x w; omega
  show mk6 _ _ _ _ _ _ = u
  rw [hk5, hk3, hs0, hs1, hs2, hs3, g0, g1, g2, g3]
  exact recon6 u hu

/-! ### The offsets

`offWords` is `{-1,0,1}^6` as 729 words; `nb u` is the closed cyclic neighbourhood of `u`,
obtained by translating `u` by each offset. -/

def offWords : List Nat :=
  ds.flatMap fun i => ds.flatMap fun j => ds.flatMap fun k => ds.flatMap fun l =>
    ds.flatMap fun m => ds.map fun n => mk6 i j k l m n

def nb (u : Nat) : List Nat := offWords.map (tadd u)

private lemma pick {a b : Nat} (ha : a < 13) (hb : b < 13) (h : sconf a b = true) :
    ∃ i ∈ ds, b = (a + i) % 13 := by
  obtain ⟨i, hi, he⟩ := List.any_eq_true.mp (sconf_cases a ha b hb h)
  exact ⟨i, hi, by simpa using he⟩

private lemma memOffW {i j k l m n : Nat} (hi : i ∈ ds) (hj : j ∈ ds) (hk : k ∈ ds)
    (hl : l ∈ ds) (hm : m ∈ ds) (hn : n ∈ ds) : mk6 i j k l m n ∈ offWords := by
  refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
  refine List.mem_flatMap.mpr ⟨j, hj, ?_⟩
  refine List.mem_flatMap.mpr ⟨k, hk, ?_⟩
  refine List.mem_flatMap.mpr ⟨l, hl, ?_⟩
  refine List.mem_flatMap.mpr ⟨m, hm, ?_⟩
  exact List.mem_map.mpr ⟨n, hn, rfl⟩

private lemma ds_lt {i : Nat} (hi : i ∈ ds) : i < 13 := by
  have h : i = 12 ∨ i = 0 ∨ i = 1 := by simpa [ds] using hi
  omega

/-- **Conflict means "is a translate by an offset".** -/
theorem mem_nb (u v : Nat) (hv : v < 4826809) (h : wconfN u v = true) : v ∈ nb u := by
  simp only [wconfN, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  obtain ⟨n, hn, e0⟩ := pick (ml _) (ml _) h0
  obtain ⟨m, hm, e1⟩ := pick (ml _) (ml _) h1
  obtain ⟨l, hl, e2⟩ := pick (ml _) (ml _) h2
  obtain ⟨k, hk, e3⟩ := pick (ml _) (ml _) h3
  obtain ⟨j, hj, e4⟩ := pick (ml _) (ml _) h4
  obtain ⟨i, hi, e5⟩ := pick (ml _) (ml _) h5
  refine List.mem_map.mpr ⟨mk6 i j k l m n, memOffW hi hj hk hl hm hn, ?_⟩
  show mk6 _ _ _ _ _ _ = v
  rw [mk6_5 (ds_lt hi) (ds_lt hj) (ds_lt hk) (ds_lt hl) (ds_lt hm) (ds_lt hn),
      mk6_4 (ds_lt hi) (ds_lt hj) (ds_lt hk) (ds_lt hl) (ds_lt hm) (ds_lt hn),
      mk6_3 (ds_lt hi) (ds_lt hj) (ds_lt hk) (ds_lt hl) (ds_lt hm) (ds_lt hn),
      mk6_2 (ds_lt hi) (ds_lt hj) (ds_lt hk) (ds_lt hl) (ds_lt hm) (ds_lt hn),
      mk6_1 (ds_lt hi) (ds_lt hj) (ds_lt hk) (ds_lt hl) (ds_lt hm) (ds_lt hn),
      mk6_0 (ds_lt hi) (ds_lt hj) (ds_lt hk) (ds_lt hl) (ds_lt hm) (ds_lt hn)]
  rw [← e5, ← e4, ← e3, ← e2, ← e1, ← e0]
  exact recon6 v hv

/-! ### The bitmask membership test -/

def memb (M u : Nat) : Bool := ((M >>> u) &&& 1) == 1

/-! ### Raw `Nat` data lifted to `Code` -/

def toCode (u : Nat) : Code := ⟨u % 4826809, Nat.mod_lt _ (by decide)⟩

theorem toCode_val {u : Nat} (h : u < 4826809) : (toCode u).val = u := Nat.mod_eq_of_lt h

theorem toCode_self (u : Code) : toCode u.val = u := Fin.ext (toCode_val u.isLt)

/-! ### Strict sortedness gives `Nodup` in linear time -/

def ssorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => (a < b) && ssorted (b :: t)

theorem ssorted_pairwise : ∀ {l : List Nat}, ssorted l = true → l.Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a t ih =>
      cases t with
      | nil => intro _; simp
      | cons b t' =>
          intro h
          simp only [ssorted, Bool.and_eq_true, decide_eq_true_eq] at h
          have hp := ih h.2
          refine List.Pairwise.cons ?_ hp
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc'
          · exact h.1
          · exact lt_trans h.1 (List.rel_of_pairwise_cons hp hc')

theorem ssorted_nodup {l : List Nat} (h : ssorted l = true) : l.Nodup :=
  (ssorted_pairwise h).imp Nat.ne_of_lt

/-- `Nodup` for the six-element tables, which are not sorted. -/
def nodupB : List Nat → Bool
  | [] => true
  | a :: t => !(t.contains a) && nodupB t

theorem nodupB_nodup : ∀ {l : List Nat}, nodupB l = true → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
      intro h
      simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
      refine List.nodup_cons.mpr ⟨?_, ih h.2⟩
      intro hc
      rw [List.contains_iff_mem.mpr hc] at h
      exact Bool.noConfusion h.1

/-! ### The `K`-invariant certificate

`S` and `S_X` list the 370 `K`-cosets of `I` and of `X`, and `pairRep` lists one private
pair per `K`-orbit of ports. -/

/-- `S = sigma(I)`, `|S| = 370`, and `169 * 370 = 62530`. -/
def Delta : List Nat := [
    1, 12, 13, 14, 25, 156, 157, 168, 169, 170, 181, 182, 183, 194, 325, 326, 337, 338,
    339, 350, 351, 352, 363, 494, 495, 506, 507, 508, 519, 520, 521, 532, 663, 664, 675, 1690,
    1691, 1702, 1703, 1704, 1715, 1846, 1847, 1858, 1859, 1860, 1871, 1872, 1873, 1884, 2015, 2016, 2027, 2028,
    2029, 2040, 2041, 2042, 2053, 2184, 2185, 2196, 2197, 2198, 2199, 2209, 2210, 2211, 2212, 2222, 2353, 2354,
    2355, 2365, 2366, 2367, 2368, 2378, 2379, 2380, 2381, 2391, 2522, 2523, 2524, 2534, 2535, 2536, 2537, 2547,
    2548, 2549, 2550, 2560, 2691, 2692, 2693, 2703, 2704, 2705, 2706, 2716, 2717, 2718, 2719, 2729, 2860, 2861,
    2862, 2872, 3887, 3888, 3889, 3899, 3900, 3901, 3902, 3912, 4043, 4044, 4045, 4055, 4056, 4057, 4058, 4068,
    4069, 4070, 4071, 4081, 4212, 4213, 4214, 4224, 4225, 4226, 4227, 4237, 4238, 4239, 4240, 4250, 4381, 4382,
    4383, 4393, 4394, 4395, 4396, 4407, 4408, 4409, 4550, 4551, 4552, 4563, 4564, 4565, 4576, 4577, 4578, 4719,
    4720, 4721, 4732, 4733, 4734, 4745, 4746, 4747, 4888, 4889, 4890, 4901, 4902, 4903, 4914, 4915, 4916, 5057,
    5058, 5059, 6084, 6085, 6086, 6097, 6098, 6099, 6240, 6241, 6242, 6253, 6254, 6255, 6266, 6267, 6268, 6409,
    6410, 6411, 6422, 6423, 6424, 6435, 6436, 6437, 6578, 6579, 6580, 6591, 6592, 6593, 6604, 6605, 6606, 6747,
    6748, 6749, 6760, 6761, 6762, 6773, 6774, 6775, 6916, 6917, 6918, 6929, 6930, 6931, 6942, 6943, 6944, 7085,
    7086, 7087, 7098, 7099, 7100, 7111, 7112, 7113, 7254, 7255, 7256, 8281, 8282, 8283, 8294, 8295, 8296, 8437,
    8438, 8439, 8450, 8451, 8452, 8463, 8464, 8465, 8606, 8607, 8608, 8619, 8620, 8621, 8632, 8633, 8634, 8775,
    8776, 8777, 21970, 21981, 21982, 21983, 21994, 21995, 22126, 22137, 22138, 22139, 22150, 22151, 22152, 22163, 22164, 22295,
    22306, 22307, 22308, 22319, 22320, 22321, 22332, 22333, 22464, 22475, 22476, 22477, 22488, 22489, 22490, 22501, 22502, 22633,
    22644, 22645, 23660, 23671, 23672, 23673, 23684, 23685, 23816, 23827, 23828, 23829, 23840, 23841, 23842, 23853, 23854, 23985,
    23996, 23997, 23998, 24009, 24010, 24011, 24022, 24023, 24154, 24165, 24166, 24167, 24178, 24179, 24180, 24191, 24192, 24323,
    24334, 24335, 24336, 24347, 24348, 24349, 24360, 24361, 24492, 24503, 24504, 24505, 24516, 24517, 24518, 24529, 24530, 24661,
    24672, 24673, 24674, 24685, 24686, 24687, 24698, 24699, 24830, 24841, 24842, 25857, 25868, 25869, 25870, 25881, 25882, 26013,
    26024, 26025, 26026, 26037, 26038, 26039, 26050, 26051, 26182, 26193, 26194, 26195, 26206, 26207, 26208, 26219, 26220, 26351,
    26362, 26363, 26364, 26365, 26375, 26376, 26377, 26378, 26388, 26389, 26520, 26521, 26531, 26532, 26533, 26534, 26544, 26545,
    26546, 26547, 26557, 26558, 26689, 26690, 26700, 26701, 26702, 26703, 26713, 26714, 26715, 26716, 26726, 26727, 26858, 26859,
    26869, 26870, 26871, 26872, 26882, 26883, 26884, 26885, 26895, 26896, 27027, 27028, 27038, 27039, 28054, 28055, 28065, 28066,
    28067, 28068, 28078, 28079, 28210, 28211, 28221, 28222, 28223, 28224, 28234, 28235, 28236, 28237, 28247, 28248, 28379, 28380,
    28390, 28391, 28392, 28393, 28403, 28404, 28405, 28406, 28416, 28417, 28548, 28549, 28559, 28560
  ]

def Sraw : List Nat := [
    5, 58, 117, 196, 444, 466, 475, 523, 602, 666, 723, 780, 824, 859, 971, 997, 1050, 1107,
    1129, 1155, 1186, 1346, 1425, 1443, 1522, 1592, 1682, 1752, 1884, 1910, 1939, 2009, 2097, 2229, 2341, 2442,
    2547, 2756, 2905, 3004, 3052, 3252, 3300, 3322, 3500, 3526, 3570, 3579, 3596, 3649, 3658, 3684, 3728, 3923,
    3941, 3985, 4055, 4233, 4268, 4290, 4312, 4396, 4534, 4543, 4613, 4648, 4758, 4813, 4971, 4975, 5065, 5076,
    5129, 5302, 5421, 5546, 5616, 5660, 5864, 6042, 6068, 6112, 6200, 6226, 6360, 6413, 6439, 6483, 6514, 6518,
    6705, 6758, 6784, 6815, 6863, 6872, 6903, 7063, 7120, 7142, 7177, 7221, 7368, 7425, 7673, 7761, 7831, 7840,
    7963, 7989, 8088, 8371, 8406, 8584, 8654, 8742, 8986, 9074, 9234, 9265, 9287, 9313, 9344, 9392, 9401, 9592,
    9614, 9618, 9649, 9671, 9719, 9737, 9763, 9897, 10046, 10136, 10303, 10312, 10373, 10382, 10492, 10560, 10687, 10718,
    10799, 10935, 11155, 11219, 11377, 11526, 11625, 11842, 11873, 11908, 11943, 12121, 12147, 12191, 12200, 12279, 12439, 12474,
    12518, 12606, 12731, 12832, 12854, 12889, 12911, 13034, 13060, 13102, 13159, 13186, 13221, 13256, 13434, 13548, 13592, 13686,
    13697, 13919, 14224, 14336, 14371, 14415, 14450, 14472, 14663, 14689, 14729, 14733, 14808, 14834, 14981, 15060, 15104, 15135,
    15203, 15352, 15374, 15392, 15471, 15480, 15535, 15605, 15684, 15693, 15741, 15763, 15798, 15963, 15989, 16215, 16226, 16277,
    16294, 16448, 16474, 16584, 16621, 16696, 16779, 16979, 17196, 17205, 17275, 17350, 17523, 17545, 17607, 17695, 17855, 17934,
    17965, 18013, 18022, 18077, 18200, 18235, 18270, 18279, 18340, 18371, 18395, 18518, 18757, 18836, 18924, 19003, 19150, 19282,
    19308, 19420, 19521, 19556, 19840, 19945, 19998, 20070, 20316, 20406, 20415, 20450, 20542, 20663, 20733, 20742, 20764, 20812,
    20821, 20937, 21047, 21069, 21095, 21126, 21286, 21365, 21396, 21453, 21475, 21532, 21655, 21692, 21710, 21850, 21949, 22011,
    22055, 22169, 22294, 22318, 22382, 22540, 22845, 22957, 22992, 23023, 23071, 23093, 23271, 23341, 23350, 23429, 23466, 23536,
    23589, 23624, 23668, 23694, 23756, 23881, 23995, 24004, 24074, 24226, 24270, 24314, 24336, 24419, 24474, 24553, 24584, 24836,
    24911, 24915, 25016, 25069, 25095, 25242, 25374, 25400, 25486, 25600, 25813, 25817, 25883, 26008, 26131, 26140, 26166, 26210,
    26289, 26353, 26397, 26476, 26485, 26555, 26698, 26755, 26803, 26812, 26856, 27003, 27060, 27082, 27130, 27139, 27161, 27365,
    27444, 27545, 27771, 27793, 27903, 27929, 28028, 28142, 28346, 28524
  ]

def SXraw : List Nat := [
    60, 91, 148, 183, 218, 253, 308, 405, 431, 545, 670, 732, 749, 850, 903, 929, 1076, 1208,
    1234, 1320, 1434, 1638, 1717, 1829, 1965, 1974, 2000, 2044, 2123, 2187, 2310, 2319, 2389, 2532, 2576, 2637,
    2646, 2690, 2725, 2824, 2850, 2903, 2951, 2973, 2995, 3199, 3278, 3379, 3605, 3614, 3737, 3763, 3862, 3976,
    4180, 4259, 4358, 4400, 4453, 4512, 4861, 4870, 4905, 4997, 5118, 5175, 5219, 5254, 5276, 5366, 5392, 5502,
    5524, 5550, 5581, 5741, 5820, 5917, 5987, 6077, 6147, 6165, 6266, 6292, 6404, 6492, 6624, 6736, 6837, 6929,
    7151, 7300, 7399, 7447, 7647, 7695, 7717, 7796, 7895, 7921, 7974, 8044, 8053, 8079, 8123, 8336, 8380, 8437,
    8459, 8663, 8685, 8707, 8791, 8929, 8938, 9008, 9039, 9043, 9153, 9291, 9366, 9370, 9471, 9524, 9697, 9816,
    9941, 10011, 10055, 10189, 10233, 10259, 10347, 10437, 10463, 10507, 10582, 10608, 10755, 10808, 10834, 10878, 10909, 10913,
    11010, 11100, 11153, 11210, 11245, 11267, 11298, 11458, 11515, 11537, 11572, 11616, 11763, 11820, 11899, 12156, 12226, 12235,
    12358, 12384, 12483, 12753, 12801, 12979, 13049, 13137, 13243, 13381, 13469, 13491, 13629, 13682, 13708, 13739, 13787, 13796,
    13987, 14009, 14013, 14044, 14053, 14114, 14132, 14158, 14292, 14362, 14441, 14698, 14707, 14755, 14777, 14887, 14955, 15025,
    15082, 15113, 15218, 15330, 15550, 15614, 15772, 15921, 16020, 16055, 16268, 16303, 16338, 16516, 16542, 16586, 16595, 16674,
    16731, 16834, 16869, 16957, 17001, 17227, 17249, 17284, 17306, 17442, 17497, 17554, 17581, 17616, 17664, 17829, 17943, 17987,
    18081, 18092, 18160, 18314, 18474, 18562, 18606, 18632, 18766, 18810, 18845, 18854, 18880, 19045, 19071, 19124, 19128, 19203,
    19229, 19376, 19455, 19499, 19530, 19534, 19598, 19734, 19756, 19787, 19831, 19866, 19888, 20079, 20088, 20136, 20158, 20193,
    20371, 20610, 20689, 20777, 20847, 20856, 20979, 21174, 21273, 21374, 21422, 21600, 21670, 21905, 21927, 21958, 22002, 22090,
    22250, 22281, 22329, 22347, 22408, 22417, 22472, 22595, 22630, 22665, 22674, 22735, 22753, 22790, 22913, 22948, 23152, 23218,
    23319, 23328, 23398, 23545, 23576, 23677, 23703, 23815, 23903, 23951, 24235, 24340, 24393, 24801, 24810, 24845, 24889, 24924,
    24959, 25137, 25194, 25216, 25332, 25442, 25464, 25490, 25521, 25747, 25791, 25848, 25857, 25905, 25927, 26050, 26105, 26245,
    26344, 26406, 26450, 26564, 26689, 26713, 26777, 26935, 27240, 27339, 27387, 27418, 27466, 27488, 27666, 27745, 27749, 27824,
    27861, 27997, 28019, 28076, 28151, 28219, 28276, 28390, 28399, 28469
  ]


def maskS : Nat := 0x1000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000004000000000000000000000000000100000000000000000000000020000008000000000000000000000000002000008000000000000000000000000000000000000000000000000000000020000000000000000000000001000000000000000000020000000000000000000000000000000000000000000000000020000080400000000000400001000000000000008000000000000000000000000000000000001000000000010080000000000080000000000000400000000000000000000000000000000000800000000000000002010000000000000000000200000000002000000000000000200000000000000000004000000000040000010080000000000000000000000000000010000000000000000000000000000000800000000000000022000000000000000000000000000000000000000000000000000010000000000000000000000000000400000000000000000000100000040000000000000000000000000000000040000000000000000000000000000000000008000002000000000000100000000000000000000000008800000000000000000100000000000000000000000000000000000000000000000000000000000000100000002000000000000000000040000000000000800000000000000000001000004000000000040000000000400000000000000000000000000000000000004000000000000000010080000000000000000000000000002000000000000000000000000000000100000000000000040000010000000000100000000200000000000010000000000000000040000000020000000000000000000402000000000000000008000000000000000000000000000000000000000000020000080000000000080000001000000002000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000004000000000000000400000400000000000000000000000000000020000000000000000000000000000800000000008000000000000002000000000000000000000000400000000000000000000000000000000004000100000000080000000000000000000000000000010000000000000080000200000000000001000000020000000000000000000400000000000000000000000000000000000000040000000800000200000800000000000000000000000000200000000000000000000000000002010000000000010000040200000000000000000800000000000000000000000000000400000000000000000000004000000008040000000000000000000001000000000000000000000000000000000000000000000000000000000000040000000000000000040000000000002000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000100000000200000000000000000000000010000000000000000000000000001000000400000000000000000000000000000000400000000000000000000000000000000000080000000000000000001000000000000000000000100000000000000000002000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000800000800000010000000000000008040000000080000000100000000000000000000000000000020000000000000402000000000002000000040000000000000000000800000000000000000000000000000000000000080000000000000000000008000000000000002000008000000000000000000000000000000000000000000400000000000000000080000000000000000201000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000008000000000000000000010000000000000000002000000001000000000000000000000000000400000100000000000000000000000000000000000000400020000000000004008000000000000000000000000000000000000000000000000000000020000008000000000000000000000000000000000000000040000000080000200000000000201000000000000000000020000000000000000080000000000001008000000000000000000100004000010000000000000000000000000000000000000800000000000000008000000100000000001000000000000000000020000000000000000000000000000000000004000001000000000000000000220000000002000000800000000000000000000000000000000000000000000001000004000000008000000000080000000100000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000020040000000000000000000000100000000001000000000000000000000000000040000000000000000000000000000000000000000000100000000200000000400000080000000000000400000000010000004000000000000000000000000000000800002000000004000010000000000000000000000000800000000000000000000000000000040000000000000000000004000000000040000000080000000000000000000000000000000000000008000000000000000000100800000000008000002000000000000000000000000000000000000000000008000000010000000020000000400000000000000000000000000000000000000000000000000000200000000000000000000000040000000000000000000000000000000000002000000000000000000000000000000000000000800000000000000080000000000000000000000000000000000000000000000000000008000000000000000000000000000000000800000000000000000004000000080000000000000000000000000000001000000000000000010000000000000000000000000004020000000000000010080000000000000000000000000000000000000000100000000000000000000004000000000000000000000000000000000000200000000000000000000000000000000080000020000800000000000800002000000044000010000000000000000000000000000000000000000000000020100000000000100000002000000800002000000040000000000000000000000000000000000000004000000000000000000000400000000000000000000000000000000000000000000000000000000000040000000000000000000004000000000000000010000000000000000000000000000000000000000000040000000080000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000200000080000000000000000000000000000010080000000000000000200000000000000000000020000000000000000000000000000000000000000000000000000000000000200000000000001000000000000000000000000000000000000200000000002000000004000010000000000000080000000000000000000000000000000000000008000000100800000000000800000010000004000000000000200000000000000000000000000000000000000000000004400000008000000000080000020000000000001000000000000000000000000000000000400000100000000000000000000010000000000100000040000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000100000000001000000000000000004000000000000000000000000000000200000000000000000000000000000400000000000000000000000000000000000000000020000000000001002000000000000000000000088000000000000000000000000000000000000002000000000000040000000000000000000000000010000000020000000000000000080400000000000000000000000000000000010000000000000000000010000040000100000000200000000000000000000000000000000000000000000800000000000000002000000000020000800000000000000000000000000000000000000000000000100000000001000000402000000000000100008040000000000400000100000000000000000000000000000000000000000000400001000000000001000000000000000000000000000000000000000000000000010000000000010000000000000000000000002000000000000000000000000000000000000100000000000000000000000000000000000000000000000000008000000000000000000000000040000000000000000000000002000000000000000000000000000200000000000000000000000000000000200000000000000000000020000000000000000080000004000001000000000000000000000000000000001000000000000000004000000000000000000000100000000000000000400000000000000000008000200000000000000000004000000000000000000000000000000000000000400000008000002000008000000000000040000000000002000000800000000000000000000000000080000000100000000001000000000000008000000000000040000000000000004000000000000000000080000000000080400001000000000000000000000000000000000000000000000000000000000000010000000000000000000200000000000000400000000000020
def maskSX : Nat := 0x20000000000000000080400000000000000000000000000010000000000000080000000000000000800000000000000000100000000000000800002000000000000000000000000000000000200000000100000000000000000022000000000000000000040000000000000000000000000000000000000000000100000400000000000400000008000000000008000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000020000000000000002000002000000000000000000000000000000100000000000000000000000000004000000000040000000000000010000000000000000000000002000000000000000000000000000000000020000000000000400000000000000000000000000000080000200000000000201000000000000008000000000080000000000000000000000000000000000000000000000000000000200000004000001000004000000000000000000000000001000000000000000000000000000010000040000000000000200000000000000000000000000000000000000000000800000001000000002000000000020000000040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000010000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000800000000000800000000000000000000080000000000000000000000000008000002000000000000000000000000100000002000000000000000000000000000000000000400000000000000001008000000000000000000000000400000000000000010000000000000000000000000000000000000000000000000010000000020000000000000000000000000000004000000002000080000000000000040200000000400000000800000000000000000000000000000100000000000002010000000000000008000200000000000200000004000000000000000000000000000000000000000400000000000000000000040000000000400000008000020000000000000000000000000000000000000000000000000000000000400000000000000001000000000000000000000000000000000000000000004000000000004000000000000000000000000200000000000000000000000040000000000000000000000000000000000000000000000008000000000000000000000000000001008000000000000000020000000000000000000002000000000000000000040000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000200000000400001000000000001008000000000000000000000000000000000000000000000010000040000000080000000000800000010000040000000000000000000000000000000004000000000000000440000000800000000008000000000000000000100000000000000000000000000000000000020000008000000000000000001100000000000008000002000000000000000000000000000000000000000010000004020000000040000000000400000000000000000000000000000000100000040000000000400000000000000000000040000000000000000000000000000000000000004000000000000000000000000000000000000010000000000000000100200000000000000000000000800000000008000000000000000000000000000200000000000000000000000000000000000000001000000000001000000002000000400000000000002000000000000040000000000000000000000000000000004000010000000020000080000000000000000000000000000000000000000000000000000000200000000002000000000000000000000200000000400000000000000000000000008000000000000040000000000000000000804000000000040000010000000000000000000000000000000000000000000040000000080000000100000000000000000000000000000000000000000000000000000800000001000000000000000000000000200000000000000000000000000000000000010000000000000000000000000000000000000004000000000000000400000000000000000000000000000000000000000000000000000040000000000000000000000000004000000000000000000000000020000000400000000000002000000000000000008000000000000000080000000000000000000000000020000080000000000080400000000000000000000000000000000000000000000000000000000000000020000000000000000000400000000000000001000000000000000000000000000000000400000100004000000000000002010000000220000080000000000000000000000000000000000000000000000100800000000000800000010000004000000000000200000000000000000000000000000000008000020000000000000000000002000000000000000000000000000000000080000000000000000000000000200000000000000000000020000000000000000080000000000000000000000000000000000000000000200000000000200000000000000000000000000000000000000000000000000000000000000000008000000000000000000000001000000400000000000000000000000000000080400000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000001000000000000008000000000000000000000000000000000001000000000010000000020000080000000000000400000000000000000000000000000000000000040000000800002000000004000000000000020000000000001000000000000000000000040000000000000000000000022000000040000000000400000100000000000008000000000000000000000000000000000001000000400000000000000000080000000000800000200000000000000000000008000000000000000000000800000200000000002000000000000000000000000000000000800000000008000000000000000020000000000000000000000000000001000000000000000000000000000002000000000000000000000000000000000000000000100000000000008000000000000000000000000440000000000000000008000000000000000000000000000000000200000000000000000000000000088000000100000000000000000402000000000000000000000000000000000080000000000000000000080000200000800000000000000000000000000000000000000000000000000800002000000000000010000000000100000000000000000000000000000000000000000000000000000800000000008000002010000000000000000040000000000002000000800000000000000000000000100000000000000000002000008000000000008000000000000000000000000000000000000000000000000080000000000080000000000000000000000010000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000020000000000000000000000200000000000000000000000010000000000000000000000000001000000000000000000000000000000001000000000000000000000100000000000000000000000000010000004000000000000000000000000200008000000000000000020000000000000000000000800000000000000002000000000000000000000001000000000000000000020000000000000000000000000000000000000002000000040000010000040000000000000000000000000010000004000000000000000000000100000400000000800000000008000000000000040000000000000000000000000000020000000000000000000000200000000402000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000002000000000000100000000004000000000000000000000000800000000000000000010000000000000000000000000000000000000000000000000010000000000000000000000000000400000000000000000000000080000020000000000000000000000000000004020000000000000000000000000000000000000000000000000000000080000000000000000000000004000000000000000000080000000000000000000000000000000000000000000000000080000200000800000000000800000000000040000010000000000000000000000002000000004000000000040200000000000000100000000001000000000000000000000000000000000002000000000000000008040000000000000000000000000000008000000000000000800000000000000000010000000000100000040200000000000000000000000000000000020000000000000000000000000002000000000000000000040000000000000000000000000000000000000000000000000040000000000000000000000000001000000000000000000000400000100000000000000000000000000000000100000000000000000000000000000000000020000008000000000000400000000000000000000000020001000000000000000400000000000000000000000000000020000000000000000000000000000800000200000000000000000000000100000000000002000000004000000008000000010000000000000080000001000000000000000


/-- The two stated generators of `K`, and `K` in closed form: `a*g1 + b*g2`. -/
def kerElt (a b : Nat) : Nat := mk6 (a % 13) (2 * a % 13) (b % 13) (11 * b % 13) 0 (a % 13)

def kerList : List Nat :=
  (List.range 13).flatMap fun a => (List.range 13).map fun b => kerElt a b

/-- **One private pair per `K`-orbit.**  Six `(parent, alternative)` pairs; the 1014 pairs
of the base are their `K`-translates.  Each alternative has exactly one `I`-conflict,
namely its parent. -/
def pairRep : List (Nat × Nat) :=
  [(1443, 4456959), (115175, 486468), (172555, 543848),
   (257592, 4713108), (257682, 628975), (344892, 716185)]

/-- `sigma(P_0)`: the six parent cosets. -/
def SPraw : List Nat := [1443, 9719, 14371, 20316, 20406, 28524]

/-- `sigma(P_1)`: the six alternative cosets. -/
def SAraw : List Nat := [5838, 5324, 9976, 24711, 16011, 24129]

/-- `sigma(X_0)`: the six cosets of `X` touched by the parent transversal. -/
def SF0raw : List Nat := [4358, 14114, 15921, 18766, 24801, 25791]

/-- `sigma(X_1)`: the six cosets of `X` touched by the alternative transversal. -/
def SF1raw : List Nat := [545, 929, 5581, 10233, 11616, 19734]

/-- One `(X`-word, representative parent`)` witness per class of `SF0raw`, in that order:
enough to show every word of `sigma^{-1}(SF0raw)` really is in the footprint. -/
def wit0 : List (Nat × Nat) :=
  [(4800408, 344892), (4570691, 115175), (628885, 257592),
   (4628071, 172555), (4713198, 257682), (372905, 1443)]

/-- The same for `SF1raw`, using the alternative transversal. -/
def wit1 : List (Nat × Nat) :=
  [(4341815, 257592), (857761, 115175), (915141, 172555),
   (4085666, 1443), (1000268, 257682), (1087478, 344892)]

/-- the translation carrying a parent to its alternative, looked up by parent coset -/
def tvec (s : Nat) : Nat :=
  match pairRep.find? (fun p => syn p.1 == s) with
  | some p => tsub p.2 p.1
  | none => 0

/-! ### The kernel certificates

Every check below runs over 6 orbit representatives, 370 cosets, 482 offsets or 729
neighbours. -/

theorem delta_card : Delta.length = 482 := by native_decide

/-- **`K` meets no nonzero offset.**  No nonzero `d` in `{-1,0,1}^6` has `sigma(d) = 0`.
This is the fact the entire syndrome reduction, and with it the `K`-descent, rests on. -/
theorem ker_meet_offsets_empty :
    offWords.all (fun o => (o == 0) || !(syn o == 0)) = true := by native_decide

/-- Every nonzero offset's syndrome is listed in `Delta`. -/
theorem sigOffCheck :
    offWords.all (fun o => (o == 0) || Delta.contains (syn o)) = true := by native_decide

/-- the numerical content of `ker_meet_offsets_empty`: `0` is not an offset syndrome -/
theorem zero_notMem_Delta : Delta.contains 0 = false := by native_decide

theorem DeltaBoundCheck : Delta.all (fun e => e < 28561) = true := by native_decide

theorem SlenCheck : Sraw.length = 370 := by native_decide
theorem SXlenCheck : SXraw.length = 370 := by native_decide
theorem SsortCheck : ssorted Sraw = true := by native_decide
theorem SXsortCheck : ssorted SXraw = true := by native_decide
theorem SboundCheck : Sraw.all (fun s => s < 28561) = true := by native_decide
theorem SXboundCheck : SXraw.all (fun s => s < 28561) = true := by native_decide

theorem SsubCheck : Sraw.all (fun s => memb maskS s) = true := by native_decide
theorem SXsubCheck : SXraw.all (fun s => memb maskSX s) = true := by native_decide

/-- **`I` is independent, at the level of cosets**: `370 * 482` mask lookups. -/
theorem SindCheck :
    Sraw.all (fun s => Delta.all (fun e => !(memb maskS (addSyn s e)))) = true := by
  native_decide

theorem SXindCheck :
    SXraw.all (fun s => Delta.all (fun e => !(memb maskSX (addSyn s e)))) = true := by
  native_decide

/-! ### The six-orbit tables -/

theorem repBoundCheck :
    pairRep.all (fun p => (p.1 < 4826809) && (p.2 < 4826809)) = true := by native_decide

/-- The tables `SPraw`, `SAraw` really are the syndromes of the representatives. -/
theorem repSynCheck :
    (((pairRep.map fun p => syn p.1) == SPraw) &&
      ((pairRep.map fun p => syn p.2) == SAraw)) = true := by native_decide

/-- `tvec` recovers the per-orbit translation from parent to alternative. -/
theorem tvecCheck :
    pairRep.all (fun p => (tvec (syn p.1) == tsub p.2 p.1) &&
      (tadd p.1 (tvec (syn p.1)) == p.2)) = true := by native_decide

theorem SPnodupCheck : nodupB SPraw = true := by native_decide
theorem SAnodupCheck : nodupB SAraw = true := by native_decide
theorem SF0nodupCheck : nodupB SF0raw = true := by native_decide
theorem SF1nodupCheck : nodupB SF1raw = true := by native_decide

theorem SPboundCheck : SPraw.all (fun s => s < 28561) = true := by native_decide
theorem SAboundCheck : SAraw.all (fun s => s < 28561) = true := by native_decide
theorem SF0boundCheck : SF0raw.all (fun s => s < 28561) = true := by native_decide
theorem SF1boundCheck : SF1raw.all (fun s => s < 28561) = true := by native_decide

theorem SPlenCheck : SPraw.length = 6 := by native_decide
theorem SF0lenCheck : SF0raw.length = 6 := by native_decide
theorem SF1lenCheck : SF1raw.length = 6 := by native_decide

/-- **`P_0 subset I`**, as six coset memberships. -/
theorem SPinSCheck : SPraw.all (fun s => Sraw.contains s) = true := by native_decide

/-- **The alternatives leave `I`**, as six coset non-memberships. -/
theorem SAnotSCheck : SAraw.all (fun s => !(Sraw.contains s)) = true := by native_decide

/-- **The alternative transversal is independent**: `6 * 482` checks. -/
theorem SAindCheck :
    SAraw.all (fun q => Delta.all (fun e => !(SAraw.contains (addSyn q e)))) = true := by
  native_decide

/-- **The two footprints are disjoint**: a `6 * 6` check. -/
theorem sepCheck : SF0raw.all (fun x => !(SF1raw.contains x)) = true := by native_decide

/-! ### Structural checks -/

/-- Each representative parent genuinely conflicts with its own alternative. -/
theorem pairConflict : pairRep.all (fun p => wconfN p.1 p.2) = true := by native_decide

/-- `sconf` is reflexive, so a repeated word would conflict with itself. -/
theorem sconf_self : ∀ a < 13, sconf a a = true := sconf_refl

/-- The two stated generators of `K` lie in `ker sigma`, and `kerElt` is their span. -/
theorem kerGenCheck :
    ((kerElt 1 0 == 428416) && (kerElt 0 1 == 4056) &&
      kerList.all (fun u => syn u == 0)) = true := by native_decide

theorem kerListLen : kerList.length = 169 := by native_decide
theorem kerListNodup : nodupB kerList = true := by native_decide

/-! ### Conflict gives a `Delta`-translate of the syndrome -/

/-- **The key consequence.**  If `u` and `v` are distinct conflicting words then their
syndromes differ by an element of `Delta`. -/
theorem syn_of_conflict (u v : Nat) (hu : u < 4826809) (hv : v < 4826809)
    (hne : v ≠ u) (h : wconfN u v = true) : ∃ e ∈ Delta, syn v = addSyn (syn u) e := by
  obtain ⟨o, ho, hov⟩ := List.mem_map.mp (mem_nb u v hv h)
  have hz : ¬ (o == 0) = true := by
    intro hzz
    rw [beq_iff_eq] at hzz
    subst hzz
    exact hne (by rw [← hov, tadd_zero u hu])
  have hd : Delta.contains (syn o) = true := by
    have hall := List.all_eq_true.mp sigOffCheck o ho
    rw [Bool.or_eq_true] at hall
    rcases hall with h1 | h1
    · exact absurd h1 hz
    · exact h1
  exact ⟨syn o, List.contains_iff_mem.mp hd, by rw [← hov, syn_tadd]⟩

/-- **Why the `K`-descent is sound.**  Distinct conflicting words never share a syndrome,
i.e. never lie in the same `K`-coset: every `K`-orbit is itself an independent set of
`C13^(box 6)`.  This is `ker_meet_offsets_empty` in the form the descent uses -- it is
what makes it legitimate to treat a whole coset as a single unit. -/
theorem syn_ne_of_conflict_of_ne (u v : Nat) (hu : u < 4826809) (hv : v < 4826809)
    (hne : v ≠ u) (h : wconfN u v = true) : syn v ≠ syn u := by
  intro heq
  obtain ⟨e, he, hev⟩ := syn_of_conflict u v hu hv hne h
  rw [heq] at hev
  have heb : e < 28561 := by
    simpa using List.all_eq_true.mp DeltaBoundCheck e he
  have h0 : e = 0 := addSyn_cancel (syn_lt u) heb hev.symm
  subst h0
  have hc : Delta.contains 0 = true := List.contains_iff_mem.mpr he
  rw [zero_notMem_Delta] at hc
  exact Bool.noConfusion hc

/-- **Independence from a coset certificate.**  If no `Delta`-translate of a listed coset
is listed, the union of the listed cosets is independent. -/
theorem indep_of_syn_gen {Sr : List Nat} (mem : Nat → Bool)
    (hsub : ∀ s ∈ Sr, mem s = true)
    (hind : ∀ s ∈ Sr, ∀ e ∈ Delta, mem (addSyn s e) = false)
    {u v : Nat} (hu : u < 4826809) (hv : v < 4826809)
    (hsu : syn u ∈ Sr) (hsv : syn v ∈ Sr) (hne : v ≠ u) : wconfN u v = false := by
  cases hw : wconfN u v with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨e, he, hev⟩ := syn_of_conflict u v hu hv hne hw
      have h1 : mem (syn v) = true := hsub _ hsv
      rw [hev, hind _ hsu e he] at h1
      exact Bool.noConfusion h1

end BaseC13
end ShannonBounds
