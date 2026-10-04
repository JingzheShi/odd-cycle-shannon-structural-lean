/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# The Polak--Schrijver base system as a `RichPortSystem` on `C7^(box 5)`

The independent set of size 367 in `C7^(box 5)` is due to Polak and Schrijver.
See the paper.

Words of `C7^5` are encoded as their base-7 code in `Fin 16807`; coordinate `k` is
`(n / 7^k) % 7`.  Conflict in `C7` is `sconf` and conflict in the strong 5th power
is `wconf` (conflict in *every* coordinate), so `G5` is `C7^(box 5)` by definition.
`CycleC7.lean` proves this for an explicitly constructed 7-cycle.

## The checks

Every check here is `native_decide`.  The coordinate conflict test is
`sconf a b := (a + 8 - b) % 7 <= 2`, tied by `sconf_eq_spec` to the literal definition
`(a - b) % 7 in {0,1,6}`, and `pairwiseOK` runs it over the unordered pairs of `Ilist`.
Because `wconf u u = true` (`sconf_refl`), `pairwiseOK Ilist = true` together with `Nodup`
certifies an independent *set* of size 367.

## The data
* `Ilist` -- the 367-word Polak--Schrijver independent set;
* `pairs` -- the 8 private pairs `(parent, alternative, side)`;
* `Xlist` -- the auxiliary set `X`.

The only `Ilist`-conflict of each alternative is its own parent, both transversals are
independent, and their footprints inside `X` are disjoint, of sizes `19` and `26`.
Hence `c = 45` and `eta = 322` (see `BaseC7.base_Xc_false`, `BaseC7.base_Xc_true`,
`BaseC7.base_eta`).
-/
import ShannonBounds.Lift

namespace ShannonBounds
namespace BaseC7

/-- Words of `C7^5`, encoded in base 7. -/
abbrev Code := Fin 16807

/-- **Reference spec** for conflict in `C7`: `(a - b) mod 7` is `0`, `1` or `6`.
(`a + 7 - b` keeps truncated `Nat` subtraction harmless for `a, b < 7`.) -/
def sconfSpec (a b : Nat) : Bool :=
  ((a + 7 - b) % 7 == 0) || ((a + 7 - b) % 7 == 1) || ((a + 7 - b) % 7 == 6)

/-- Equivalently: `{0,1,6}` shifted up by one mod 7 is `{x | x <= 2}`. -/
def sconf (a b : Nat) : Bool := (a + 8 - b) % 7 <= 2

theorem sconf_eq_spec : ∀ a < 7, ∀ b < 7, sconf a b = sconfSpec a b := by native_decide
theorem sconf_symm : ∀ a < 7, ∀ b < 7, sconf a b = sconf b a := by native_decide
theorem sconf_refl : ∀ a < 7, sconf a a = true := by native_decide

/-- Coordinate `k` of a code, as a `Nat`, for `m = 7^k`. -/
def dgt (m : Nat) (u : Code) : Nat := u.val / m % 7

lemma dgt_lt (m : Nat) (u : Code) : dgt m u < 7 := Nat.mod_lt _ (by decide)

/-- Conflict in `C7^(box 5)`: conflict in every one of the five coordinates. -/
def wconf (u v : Code) : Bool :=
  sconf (dgt 1 u) (dgt 1 v) && sconf (dgt 7 u) (dgt 7 v) && sconf (dgt 49 u) (dgt 49 v) &&
    sconf (dgt 343 u) (dgt 343 v) && sconf (dgt 2401 u) (dgt 2401 v)

lemma wconf_symm (u v : Code) : wconf u v = wconf v u := by
  unfold wconf
  rw [sconf_symm (dgt 1 u) (dgt_lt 1 u) (dgt 1 v) (dgt_lt 1 v),
    sconf_symm (dgt 7 u) (dgt_lt 7 u) (dgt 7 v) (dgt_lt 7 v),
    sconf_symm (dgt 49 u) (dgt_lt 49 u) (dgt 49 v) (dgt_lt 49 v),
    sconf_symm (dgt 343 u) (dgt_lt 343 u) (dgt 343 v) (dgt_lt 343 v),
    sconf_symm (dgt 2401 u) (dgt_lt 2401 u) (dgt 2401 v) (dgt_lt 2401 v)]

lemma wconf_refl (u : Code) : wconf u u = true := by
  unfold wconf
  rw [sconf_refl (dgt 1 u) (dgt_lt 1 u), sconf_refl (dgt 7 u) (dgt_lt 7 u),
    sconf_refl (dgt 49 u) (dgt_lt 49 u), sconf_refl (dgt 343 u) (dgt_lt 343 u),
    sconf_refl (dgt 2401 u) (dgt_lt 2401 u)]
  rfl

/-- `C7^(box 5)`. -/
def G5 : SimpleGraph Code where
  Adj u v := u ≠ v ∧ wconf u v = true
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by rw [wconf_symm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance decG5 : DecidableRel G5.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ wconf u v = true))

lemma conflict_G5 (u v : Code) : conflict G5 u v ↔ wconf u v = true := by
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · exact wconf_refl u
    · exact h
  · intro h
    by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr ⟨huv, h⟩

/-! ### Independence as a one-directional `Bool` check -/

def pairwiseOK : List Code → Bool
  | [] => true
  | u :: us => us.all (fun v => !(wconf u v)) && pairwiseOK us

lemma pairwiseOK_forall {l : List Code} (h : pairwiseOK l = true) :
    ∀ x ∈ l, ∀ y ∈ l, x ≠ y → wconf x y = false := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons u rest ih =>
      simp only [pairwiseOK, Bool.and_eq_true] at h
      intro x hx y hy hne
      rcases List.mem_cons.mp hx with rfl | hx'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd rfl hne
        · simpa using List.all_eq_true.mp h.1 y hy'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rw [wconf_symm]
          simpa using List.all_eq_true.mp h.1 x hx'
        · exact ih h.2 x hx' y hy' hne

lemma isIndepSet_of_pairwiseOK {l : List Code} {nd : (l : Multiset Code).Nodup}
    (h : pairwiseOK l = true) :
    G5.IsIndepSet ((⟨(l : Multiset Code), nd⟩ : Finset Code) : Set Code) := by
  intro x hx y hy hne
  rw [Finset.mem_coe, Finset.mem_mk, Multiset.mem_coe] at hx hy
  intro hadj
  have h2 : wconf x y = true := hadj.2
  rw [pairwiseOK_forall h x hx y hy hne] at h2
  exact Bool.false_ne_true h2

/-! ### The data -/

def Ilist : List Code :=
  [
    700, 5208, 9716, 14567, 4669, 9177, 13692, 1393, 5852, 10360, 15211, 2912, 7420, 11054,
    3557, 8065, 12573, 617, 5132, 11698, 16549, 4250, 8758, 1261, 5769, 10284, 14792, 2493,
    9402, 13910, 1954, 6462, 15730, 3088, 7596, 12104, 148, 7057, 11565, 16423, 3781, 8240,
    12748, 792, 5300, 9808, 14659, 4768, 8933, 13441, 1485, 5944, 10452, 15303, 3004, 7519,
    14085, 2129, 6637, 11145, 15996, 3648, 373, 4881, 11790, 16641, 4342, 8850, 1360, 5525,
    10033, 14884, 2585, 9494, 14002, 2053, 6218, 10677, 15528, 3229, 7737, 12245, 289, 7156,
    11321, 16172, 3873, 8332, 12840, 884, 5392, 9907, 14415, 4517, 9025, 13533, 1577, 6036,
    15402, 2760, 7268, 14177, 2221, 6729, 11237, 3747, 7912, 12420, 464, 4972, 11881, 16732,
    1109, 5617, 10125, 14976, 2677, 9593, 13758, 1802, 6310, 10769, 15620, 3321, 7829, 12344,
    45, 6954, 11462, 16313, 4014, 8473, 983, 5148, 9656, 14507, 4609, 9117, 13625, 6135,
    10300, 15151, 2852, 7360, 14269, 2313, 6828, 10993, 3496, 8004, 12512, 556, 5064, 11980,
    16488, 4189, 8697, 13156, 1200, 5708, 15075, 2433, 9342, 13850, 1894, 6402, 10861, 15712,
    3420, 7585, 12093, 137, 7046, 11554, 16405, 8572, 12737, 781, 5289, 9797, 14648, 4750,
    9216, 13381, 5884, 10392, 15243, 2944, 7452, 14368, 2069, 6577, 11085, 3588, 8096, 12604,
    655, 4820, 11729, 16580, 4281, 8789, 13248, 5807, 9972, 14823, 2524, 9433, 13941, 1985,
    10960, 15468, 3169, 7677, 12185, 229, 7138, 11653, 16161, 3862, 8321, 12829, 873, 5381,
    9889, 14747, 4506, 9014, 13522, 6025, 10533, 15384, 3043, 7208, 14117, 2161, 6669, 11177,
    8195, 12360, 404, 4912, 11821, 4373, 8888, 13347, 1048, 5556, 10064, 14040, 10708, 6012,
    10520, 15371, 3079, 7244, 2197, 6705, 11213, 16064, 8231, 440, 4948, 11857, 16708, 4409,
    8875, 13677, 1035, 5543, 10051, 14902, 2603, 9512, 1728, 6236, 10695, 15546, 3247, 7755,
    314, 6880, 11388, 16239, 3940, 8399, 951, 5466, 9631, 14482, 4584, 9092, 13600, 1644,
    6110, 15120, 2821, 7329, 2282, 6790, 11305, 3465, 7973, 525, 5033, 11942, 16800, 4158,
    8666, 1169, 5677, 10185, 15036, 2695, 9261, 13769, 1813, 6321, 10780, 15631, 7847, 56,
    6965, 11473, 16324, 4025, 12999, 3332, 12012, 8491, 14329, 6545, 14238, 10612, 2380, 15813,
    12824, 10879, 15905, 13266, 10551, 12672, 4440, 15795, 13065, 8606, 12981, 1376, 15887, 1292,
    10217, 4106, 3680, 16329, 215, 9525, 1741, 6249, 859, 5367, 1566, 12263, 12907, 11402,
    1553, 12095, 12739
  ]

def Xlist : List Code :=
  [
    700, 5152, 9604, 16464, 4158, 8610, 13068, 720, 5515, 9967, 14426, 4472, 8924, 10029,
    2476, 9329, 13781, 1433, 5884, 10385, 14844, 2489, 9342, 1789, 6241, 10692, 15151, 2796,
    7297, 14150, 1802, 6254, 15507, 3152, 7604, 12056, 2109, 6610, 11062, 15520, 3165, 7960,
    12412, 64, 6917, 11369, 15828, 3521, 7973, 12425, 77, 4872, 11725, 16184, 3829, 8287,
    12788, 440, 4892, 11745, 16204, 4192, 796, 5248, 9749, 16609, 4254, 8706, 1152, 5604,
    10056, 14515, 4561, 9062, 13514, 1165, 5617, 10412, 14871, 2516, 9369, 13821, 1473, 5973,
    10425, 14884, 2529, 7324, 14177, 1829, 6281, 10732, 15191, 2885, 7337, 14190, 1842, 6637,
    15547, 3192, 7644, 12145, 2198, 6650, 11102, 3555, 8007, 12459, 111, 6964, 11465, 15924,
    516, 4968, 11821, 16280, 3925, 8425, 12877, 529, 4981, 9776, 16636, 4281, 8733, 13184,
    836, 5337, 9789, 16649, 4294, 9089, 1192, 5644, 10096, 14555, 4650, 9102, 13554, 6000,
    10452, 14911, 2556, 9409, 13910, 1562, 6013, 10465, 2912, 7364, 14217, 1869, 6321, 10828,
    15287, 2932, 7384, 12179, 2232, 6684, 15643, 3288, 7789, 12241, 2294, 6746, 11541, 16000,
    3644, 8096, 12548, 200, 7102, 11554, 16013, 8452, 12904, 556, 5008, 11861, 16320, 4014,
    8465, 12917, 5364, 9816, 16676, 4321, 8773, 13273, 925, 5377, 9829, 4677, 9129, 13581,
    1232, 5684, 10185, 14644, 4690, 9142, 13937, 6047, 10499, 14958, 2603, 9505, 13957, 1609,
    10904, 15363, 3008, 7460, 14313, 1965, 6466, 10917, 15376, 3021, 7816, 12268, 2321, 6773,
    11225, 15683, 3377, 7829, 12281, 7129, 11581, 16040, 3684, 8136, 12637, 289, 7142, 11594,
    8492, 12944, 596, 5048, 11950, 4054, 8505, 13300, 952, 5404, 9856, 13320, 10219, 7180,
    11632, 16091, 3735, 8187, 340, 7193, 11645, 16104, 8543, 647, 5099, 12001, 16460, 4105,
    8556, 13364, 1003, 5455, 9907, 16767, 4412, 8913, 1016, 5468, 10263, 14722, 4768, 9220,
    1323, 5824, 10276, 14735, 4781, 9576, 1680, 6138, 10590, 15049, 2743, 9596, 14048, 1700,
    4092, 15111, 2756, 7208, 1762, 6214, 10665, 3112, 7564, 2069, 6521, 11022, 15480, 3125,
    7577, 24, 6877, 11329, 15788, 3432, 7933, 12385, 37, 6890, 11685, 16144, 8240, 344,
    4845, 11698, 16157, 3802, 13048, 3789, 12692, 8596, 13425, 5528, 14110, 10652, 1076, 15124,
    12023, 11048, 14488, 13794, 11088, 13144, 3568, 15267, 12864, 8069, 13541, 912, 14631, 1589,
    11185, 3658, 4041, 16402, 1960, 8862, 972, 5424, 2323, 6775, 2334, 13672, 14028, 10281,
    2385, 12646, 13002
  ]

/-- The eight private pairs `(parent, alternative, side)`. -/
def pairs : List (Code × Code × Bool) :=
  [(15996, 16046, true), (13065, 13358, false), (10708, 13158, false), (15075, 14733, false), (13677, 14027, false), (14329, 12277, true), (1553, 15910, true), (6110, 3716, false)]

def portsList : List Code := [15996, 13065, 10708, 15075, 13677, 14329, 1553, 6110]

def Iset : Finset Code := ⟨(Ilist : Multiset Code), by native_decide⟩
def Xset : Finset Code := ⟨(Xlist : Multiset Code), by native_decide⟩
def portsSet : Finset Code := ⟨(portsList : Multiset Code), by native_decide⟩

def bside (r : Code) : Bool :=
  match pairs.find? (fun t => t.1.val == r.val) with
  | some t => t.2.2
  | none => false

def bep (c : Bool) (r : Code) : Code :=
  match pairs.find? (fun t => t.1.val == r.val) with
  | some t => if c == t.2.2 then r else t.2.1
  | none => r

/-! ### Independence of `I` and of `X` -/

theorem pairwiseOK_I : pairwiseOK Ilist = true := by native_decide
theorem pairwiseOK_X : pairwiseOK Xlist = true := by native_decide

/-! ### The private pairs are edges, and both transversals are independent -/

/-- Each parent conflicts with its own alternative, so every private pair is an edge;
this discharges `RichPortSystem.hep_conflict` (see `BaseC7.h_ep_conflict`). -/
theorem pairConflict :
    portsList.all (fun r => wconf (bep (bside r) r) (bep (!bside r) r)) = true := by
  native_decide

/-- Both transversals used here are independent. -/
theorem transversal_false_indep : pairwiseOK (portsList.map (bep false)) = true := by
  native_decide

theorem transversal_true_indep : pairwiseOK (portsList.map (bep true)) = true := by
  native_decide

end BaseC7
end ShannonBounds
