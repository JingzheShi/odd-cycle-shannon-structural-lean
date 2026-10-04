/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# Rich port systems and the combined-inheritance lift

## The definition used here

The transversals are genuinely free: `ep c r` is the endpoint of the pair `r` on
transversal `c : Bool`, and `side r` records which transversal carries the *parent*.
So `ep (side r) r = r ∈ I` and `alt r := ep (!side r) r ∉ I`, but which of the two
labels `0`/`1` gets the parent varies from pair to pair.  Both transversals must be
independent (`hP_indep`).

The *footprint classes* `Xc c` are the words of `X` conflicting with some `P c`
endpoint; `hsep` says the two footprints are disjoint, and
`Xstar = X \ (Xc false ∪ Xc true)` is the neutral part, so `eta = |Xstar|`.

## Privacy is a set equality, in both directions

The paper asks of a valid tuple that `N[ep c r] ∩ I = {s}` for both endpoints `c`.
Together, `hprivate` and `hep_conflict` imply the required neighbourhood equality, and
`RichPortSystem.conflict_ep_iff` states it.  So the structure is exactly the paper's
notion of a valid tuple, and `lift_closure` is literally the paper's closure theorem.

## The strip rule has three cases

`cls x` is `some c` when `x ∈ Xc c` and `none` when `x` is neutral.  The horizontal
strip at a `T`-pair `r` uses `T.epO (S.cls x) r`: the `P false` endpoint on the `false`
footprint, the `P true` endpoint on the `true` footprint, and **the parent** for a
neutral word.  The vertical strip uses the **opposite** endpoint,
`S.epO ((T.cls y).map not) t`.

## Main results

* `isIndepSet_liftSet` : `liftSet S T` is independent in `strongProd G₁ G₂`.
  Unconditional.
* `card_liftX` : `L' = L*K`;  `card_liftNeutral` : `eta' = eta*zeta + (L-eta)*(K-zeta)`;
  `card_liftPorts` : `d' = eta*e + d*zeta`;
  `card_liftSet` : `N' = (N-d)*(M-e) + L*e + d*K`.
* `liftEp_conflict` : the lifted pairs are edges again, so `hep_conflict` survives.
* `liftRPS` / `lift_closure` : the lifted data is again a `RichPortSystem`, with
  exactly those parameters.  So the invariant is closed under the lift.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod

namespace ShannonBounds

variable {V : Type*} [DecidableEq V]

/-- `conflict G x y`: equal, or adjacent.  Non-confusability is its negation. -/
def conflict (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Prop :=
  x = y ∨ G.Adj x y

instance decidableConflict (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (conflict G) := fun x y => decidable_of_iff (x = y ∨ G.Adj x y) Iff.rfl

lemma bool_eq_or_eq_not (c b : Bool) : c = b ∨ c = !b := by
  cases c <;> cases b <;> simp

section ConflictBasic

variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma conflict_rfl (x : V) : conflict G x x := Or.inl rfl

omit [DecidableEq V] in
lemma conflict_symm {x y : V} (h : conflict G x y) : conflict G y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

omit [DecidableEq V] in
lemma ne_of_not_conflict {x y : V} (h : ¬ conflict G x y) : x ≠ y := fun he => h (Or.inl he)

omit [DecidableEq V] in
/-- Conflicting members of an independent set are equal. -/
lemma eq_of_conflict_of_indep {s : Finset V} (hs : G.IsIndepSet (s : Set V)) {x y : V}
    (hx : x ∈ s) (hy : y ∈ s) (h : conflict G x y) : x = y := by
  rcases h with h | h
  · exact h
  · exact absurd h (hs (by simpa using hx) (by simpa using hy) h.ne)

omit [DecidableEq V] in
lemma not_conflict_of_indep {s : Finset V} (hs : G.IsIndepSet (s : Set V)) {x y : V}
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) : ¬ conflict G x y :=
  fun h => hne (eq_of_conflict_of_indep hs hx hy h)

end ConflictBasic

/-- A *rich* port system.  See the module docstring. -/
structure RichPortSystem (G : SimpleGraph V) [DecidableRel G.Adj] where
  I          : Finset V
  hI         : G.IsIndepSet ↑I
  /-- the parents; `d = |ports|` -/
  ports      : Finset V
  hports     : ports ⊆ I
  /-- `ep c r` is the endpoint of the private pair `r` lying on transversal `c` -/
  ep         : Bool → V → V
  /-- which transversal carries the parent of the pair -/
  side       : V → Bool
  hep_parent : ∀ r ∈ ports, ep (side r) r = r
  /-- the other endpoint leaves `I` -/
  halt_not   : ∀ r ∈ ports, ep (!side r) r ∉ I
  /-- *private*: the only `I`-vertex conflicting with the other endpoint is `r` -/
  hprivate   : ∀ r ∈ ports, ∀ w ∈ I, conflict G (ep (!side r) r) w → w = r
  /-- *the pair is an edge*: the parent really does conflict with its own alternative.
  `hprivate` bounds `N[alt r] ∩ I` above by `{r}`; this bounds it below, so together
  they give the set **equality** `N[alt r] ∩ I = {r}` that the paper demands.  For the
  other endpoint `ep (side r) r = r` the same equality is automatic from `hI`. -/
  hep_conflict : ∀ r ∈ ports, conflict G r (ep (!side r) r)
  /-- distinct pairs have distinct alternatives -/
  halt_inj   : ∀ r ∈ ports, ∀ s ∈ ports, ep (!side r) r = ep (!side s) s → r = s
  /-- **both** transversals are independent -/
  hP_indep   : ∀ c : Bool, ∀ r ∈ ports, ∀ s ∈ ports, r ≠ s → ¬ conflict G (ep c r) (ep c s)
  X          : Finset V
  hX         : G.IsIndepSet ↑X
  /-- *separation*: the two endpoint footprints inside `X` are disjoint -/
  hsep       : ∀ x ∈ X, ¬ ((∃ r ∈ ports, conflict G x (ep false r)) ∧
                            (∃ r ∈ ports, conflict G x (ep true r)))

namespace RichPortSystem

variable {G : SimpleGraph V} [DecidableRel G.Adj] (S : RichPortSystem G)

/-- The alternative endpoint of the pair `r`. -/
def alt (r : V) : V := S.ep (!S.side r) r

/-- The footprint class `X_c`: words of `X` conflicting with some `P c`-endpoint. -/
def Xc (c : Bool) : Finset V := S.X.filter fun x => ∃ r ∈ S.ports, conflict G x (S.ep c r)

/-- The neutral part `X_*`: words of `X` avoiding every endpoint. -/
def Xstar : Finset V := S.X \ (S.Xc false ∪ S.Xc true)

/-- The four numerical parameters `(N, d, L, eta)`. -/
def N : ℕ := S.I.card
def d : ℕ := S.ports.card
def L : ℕ := S.X.card
def eta : ℕ := S.Xstar.card

lemma mem_Xc {c : Bool} {x : V} :
    x ∈ S.Xc c ↔ x ∈ S.X ∧ ∃ r ∈ S.ports, conflict G x (S.ep c r) := Finset.mem_filter

lemma Xc_subset_X (c : Bool) : S.Xc c ⊆ S.X := Finset.filter_subset _ _

lemma Xstar_subset_X : S.Xstar ⊆ S.X := Finset.sdiff_subset

lemma mem_Xstar {x : V} : x ∈ S.Xstar ↔ x ∈ S.X ∧ x ∉ S.Xc false ∧ x ∉ S.Xc true := by
  rw [Xstar, Finset.mem_sdiff, Finset.mem_union, not_or]

lemma mem_Xc_of_conflict {x : V} (hx : x ∈ S.X) {c : Bool} {r : V} (hr : r ∈ S.ports)
    (h : conflict G x (S.ep c r)) : x ∈ S.Xc c := S.mem_Xc.mpr ⟨hx, r, hr, h⟩

/-- **Separation.** The two footprint classes are disjoint. -/
lemma Xc_disjoint : Disjoint (S.Xc false) (S.Xc true) := by
  rw [Finset.disjoint_left]
  intro x h0 h1
  obtain ⟨hx, r, hr, hcr⟩ := S.mem_Xc.mp h0
  obtain ⟨-, s, hs, hcs⟩ := S.mem_Xc.mp h1
  exact S.hsep x hx ⟨⟨r, hr, hcr⟩, ⟨s, hs, hcs⟩⟩

lemma notMem_Xc_of_mem_Xc {c : Bool} {x : V} (h : x ∈ S.Xc c) : x ∉ S.Xc (!c) := by
  cases c
  · exact Finset.disjoint_left.mp S.Xc_disjoint h
  · exact fun h' => Finset.disjoint_left.mp S.Xc_disjoint h' h

/-- A neutral word avoids every endpoint. -/
lemma not_conflict_ep_of_mem_Xstar {x : V} (hx : x ∈ S.Xstar) (c : Bool) {r : V}
    (hr : r ∈ S.ports) : ¬ conflict G x (S.ep c r) := by
  intro h
  obtain ⟨hxX, h0, h1⟩ := S.mem_Xstar.mp hx
  cases c
  · exact h0 (S.mem_Xc_of_conflict hxX hr h)
  · exact h1 (S.mem_Xc_of_conflict hxX hr h)

lemma notMem_ports_of_mem_Xstar {x : V} (hx : x ∈ S.Xstar) : x ∉ S.ports := by
  intro hp
  refine S.not_conflict_ep_of_mem_Xstar hx (S.side x) hp ?_
  rw [S.hep_parent x hp]
  exact conflict_rfl x

omit [DecidableEq V] in
/-- A core word is non-confusable with every endpoint. -/
lemma not_conflict_core_ep {w : V} (hw : w ∈ S.I) (hwp : w ∉ S.ports) (c : Bool)
    {r : V} (hr : r ∈ S.ports) : ¬ conflict G w (S.ep c r) := by
  rcases bool_eq_or_eq_not c (S.side r) with hc | hc
  · rw [hc, S.hep_parent r hr]
    exact not_conflict_of_indep S.hI hw (S.hports hr) (fun he => hwp (by rw [he]; exact hr))
  · rw [hc]
    intro h
    exact hwp (by rw [S.hprivate r hr w hw (conflict_symm h)]; exact hr)

/-! ### The three-case endpoint selector -/

/-- `epO none r` is the parent `r`; `epO (some c) r` is the `P c` endpoint. -/
def epO (o : Option Bool) (r : V) : V := match o with | none => r | some c => S.ep c r

omit [DecidableEq V] in
@[simp] lemma epO_none (r : V) : S.epO none r = r := rfl
omit [DecidableEq V] in
@[simp] lemma epO_some (c : Bool) (r : V) : S.epO (some c) r = S.ep c r := rfl

omit [DecidableEq V] in
lemma epO_eq_ep {r : V} (hr : r ∈ S.ports) (o : Option Bool) :
    S.epO o r = S.ep (o.getD (S.side r)) r := by
  cases o with
  | none => exact (S.hep_parent r hr).symm
  | some c => rfl

/-- The class of a word of `X`: `some c` on the footprint of `P c`, `none` if neutral. -/
def cls (x : V) : Option Bool :=
  if x ∈ S.Xc false then some false else if x ∈ S.Xc true then some true else none

lemma cls_eq_some_of_mem_Xc {c : Bool} {x : V} (h : x ∈ S.Xc c) : S.cls x = some c := by
  cases c
  · rw [cls, if_pos h]
  · have h0 : x ∉ S.Xc false := S.notMem_Xc_of_mem_Xc h
    rw [cls, if_neg h0, if_pos h]

lemma cls_eq_none_of_mem_Xstar {x : V} (h : x ∈ S.Xstar) : S.cls x = none := by
  obtain ⟨-, h0, h1⟩ := S.mem_Xstar.mp h
  rw [cls, if_neg h0, if_neg h1]

lemma mem_Xstar_of_cls_eq_none {x : V} (hx : x ∈ S.X) (h : S.cls x = none) : x ∈ S.Xstar := by
  refine S.mem_Xstar.mpr ⟨hx, ?_, ?_⟩
  · intro h0
    rw [S.cls_eq_some_of_mem_Xc h0] at h
    simp at h
  · intro h1
    rw [S.cls_eq_some_of_mem_Xc h1] at h
    simp at h

lemma mem_Xc_of_conflict_epO {x : V} (hx : x ∈ S.X) {o : Option Bool} {r : V}
    (hr : r ∈ S.ports) (h : conflict G x (S.epO o r)) : x ∈ S.Xc (o.getD (S.side r)) := by
  rw [S.epO_eq_ep hr] at h
  exact S.mem_Xc_of_conflict hx hr h

omit [DecidableEq V] in
/-- Endpoints selected by the *same* rule at distinct pairs are non-confusable. -/
lemma not_conflict_epO_epO (o : Option Bool) {r s : V} (hr : r ∈ S.ports) (hs : s ∈ S.ports)
    (hrs : r ≠ s) : ¬ conflict G (S.epO o r) (S.epO o s) := by
  cases o with
  | none => exact not_conflict_of_indep S.hI (S.hports hr) (S.hports hs) hrs
  | some c => exact S.hP_indep c r hr s hs hrs

omit [DecidableEq V] in
lemma not_conflict_core_epO {w : V} (hw : w ∈ S.I) (hwp : w ∉ S.ports) (o : Option Bool)
    {r : V} (hr : r ∈ S.ports) : ¬ conflict G w (S.epO o r) := by
  rw [S.epO_eq_ep hr]
  exact S.not_conflict_core_ep hw hwp _ hr

lemma not_conflict_epO_of_mem_Xstar {x : V} (hx : x ∈ S.Xstar) (o : Option Bool) {r : V}
    (hr : r ∈ S.ports) : ¬ conflict G x (S.epO o r) := by
  rw [S.epO_eq_ep hr]
  exact S.not_conflict_ep_of_mem_Xstar hx _ hr

omit [DecidableEq V] in
lemma alt_eq (r : V) : S.alt r = S.ep (!S.side r) r := rfl

omit [DecidableEq V] in
lemma alt_notMem_I {r : V} (hr : r ∈ S.ports) : S.alt r ∉ S.I := S.halt_not r hr

omit [DecidableEq V] in
/-- **The paper's private-pair condition, as the set equality it is.**  For *both*
endpoints `c` of the pair at `r`, the `I`-vertices conflicting with `ep c r` are exactly
`{r}`, i.e. `N[ep c r] ∩ I = {r}`.  For `c = side r` this is independence of `I`; for
`c = !side r` it is `hprivate` (⊆) together with `hep_conflict` (⊇). -/
lemma conflict_ep_iff {r : V} (hr : r ∈ S.ports) (c : Bool) {w : V} (hw : w ∈ S.I) :
    conflict G (S.ep c r) w ↔ w = r := by
  rcases bool_eq_or_eq_not c (S.side r) with hc | hc
  · rw [hc, S.hep_parent r hr]
    constructor
    · intro h
      exact (eq_of_conflict_of_indep S.hI (S.hports hr) hw h).symm
    · intro h
      rw [h]
      exact conflict_rfl r
  · rw [hc]
    constructor
    · exact S.hprivate r hr w hw
    · intro h
      rw [h]
      exact conflict_symm (S.hep_conflict r hr)

end RichPortSystem

section Lift

variable {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
variable {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
variable [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]

/-- The strong product: adjacent iff distinct and conflicting in both coordinates. -/
def strongProd (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] : SimpleGraph (V₁ × V₂) where
  Adj p q := p ≠ q ∧ conflict G₁ p.1 q.1 ∧ conflict G₂ p.2 q.2
  symm := ⟨by
    intro p q ⟨hne, h1, h2⟩
    exact ⟨hne.symm, conflict_symm h1, conflict_symm h2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [DecidableEq V₁] [DecidableEq V₂] in
lemma strongProd_adj {p q : V₁ × V₂} :
    (strongProd G₁ G₂).Adj p q ↔ p ≠ q ∧ conflict G₁ p.1 q.1 ∧ conflict G₂ p.2 q.2 :=
  Iff.rfl

instance decidableStrongProdAdj : DecidableRel (strongProd G₁ G₂).Adj := fun _ _ =>
  decidable_of_iff _ strongProd_adj.symm

/-- Conflict in a strong product is conflict in each coordinate. -/
lemma conflict_strongProd_iff {p q : V₁ × V₂} :
    conflict (strongProd G₁ G₂) p q ↔ conflict G₁ p.1 q.1 ∧ conflict G₂ p.2 q.2 := by
  constructor
  · rintro (rfl | ⟨-, h1, h2⟩)
    · exact ⟨conflict_rfl _, conflict_rfl _⟩
    · exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    by_cases hpq : p = q
    · exact Or.inl hpq
    · exact Or.inr ⟨hpq, h1, h2⟩

lemma conflict_fst {p q : V₁ × V₂} (h : conflict (strongProd G₁ G₂) p q) :
    conflict G₁ p.1 q.1 := (conflict_strongProd_iff.mp h).1

lemma conflict_snd {p q : V₁ × V₂} (h : conflict (strongProd G₁ G₂) p q) :
    conflict G₂ p.2 q.2 := (conflict_strongProd_iff.mp h).2

omit [DecidableEq V₁] [DecidableEq V₂] in
lemma not_adj_strongProd (p q : V₁ × V₂)
    (h : ¬ conflict G₁ p.1 q.1 ∨ ¬ conflict G₂ p.2 q.2) :
    ¬ (strongProd G₁ G₂).Adj p q := by
  rintro ⟨-, h1, h2⟩
  rcases h with h | h
  · exact h h1
  · exact h h2

open RichPortSystem

/-- The *core*: non-parent words in both coordinates.  Size `(N-d)(M-e)`. -/
def core (S : RichPortSystem G₁) (T : RichPortSystem G₂) : Finset (V₁ × V₂) :=
  (S.I \ S.ports) ×ˢ (T.I \ T.ports)

/-- The *horizontal strip* at a `T`-pair `r`: for `x ∈ X_S` the endpoint dictated by
the class of `x` (the parent when `x` is neutral). -/
def hstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂) (r : V₂) : Finset (V₁ × V₂) :=
  S.X.image fun x => (x, T.epO (S.cls x) r)

/-- The *vertical strip* at an `S`-pair `t`: the **opposite** endpoint. -/
def vstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂) (t : V₁) : Finset (V₁ × V₂) :=
  T.X.image fun y => (S.epO ((T.cls y).map Bool.not) t, y)

/-- The lifted set. -/
def liftSet (S : RichPortSystem G₁) (T : RichPortSystem G₂) : Finset (V₁ × V₂) :=
  core S T ∪ T.ports.biUnion (hstrip S T) ∪ S.ports.biUnion (vstrip S T)

/-! ### Membership lemmas -/

lemma mem_core (S : RichPortSystem G₁) (T : RichPortSystem G₂) {p : V₁ × V₂} :
    p ∈ core S T ↔ (p.1 ∈ S.I ∧ p.1 ∉ S.ports) ∧ (p.2 ∈ T.I ∧ p.2 ∉ T.ports) := by
  rw [core, Finset.mem_product, Finset.mem_sdiff, Finset.mem_sdiff]

lemma mem_hstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂) (r : V₂) {p : V₁ × V₂} :
    p ∈ hstrip S T r ↔ p.1 ∈ S.X ∧ p.2 = T.epO (S.cls p.1) r := by
  constructor
  · intro hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hx, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Finset.mem_image.mpr ⟨p.1, h1, Prod.ext rfl h2.symm⟩

lemma mem_vstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂) (t : V₁) {p : V₁ × V₂} :
    p ∈ vstrip S T t ↔ p.2 ∈ T.X ∧ p.1 = S.epO ((T.cls p.2).map Bool.not) t := by
  constructor
  · intro hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hy, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Finset.mem_image.mpr ⟨p.2, h1, Prod.ext h2.symm rfl⟩

lemma mem_core_mk (S : RichPortSystem G₁) (T : RichPortSystem G₂) {a : V₁} {b : V₂} :
    (a, b) ∈ core S T ↔ (a ∈ S.I ∧ a ∉ S.ports) ∧ (b ∈ T.I ∧ b ∉ T.ports) := mem_core S T

lemma mem_hstrip_mk (S : RichPortSystem G₁) (T : RichPortSystem G₂) (r : V₂)
    {a : V₁} {b : V₂} :
    (a, b) ∈ hstrip S T r ↔ a ∈ S.X ∧ b = T.epO (S.cls a) r := mem_hstrip S T r

lemma mem_vstrip_mk (S : RichPortSystem G₁) (T : RichPortSystem G₂) (t : V₁)
    {a : V₁} {b : V₂} :
    (a, b) ∈ vstrip S T t ↔ b ∈ T.X ∧ a = S.epO ((T.cls b).map Bool.not) t := mem_vstrip S T t

lemma mem_liftSet (S : RichPortSystem G₁) (T : RichPortSystem G₂) {p : V₁ × V₂} :
    p ∈ liftSet S T ↔ p ∈ core S T ∨
      (∃ r ∈ T.ports, p ∈ hstrip S T r) ∨ (∃ t ∈ S.ports, p ∈ vstrip S T t) := by
  simp only [liftSet, Finset.mem_union, Finset.mem_biUnion, or_assoc]

/-! ### The pieces of the independence argument -/

lemma not_conflict_core_hstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂)
    {r : V₂} (hr : r ∈ T.ports) {p q : V₁ × V₂}
    (hp : p ∈ core S T) (hq : q ∈ hstrip S T r) : ¬ conflict G₂ p.2 q.2 := by
  obtain ⟨-, hpI, hpP⟩ := (mem_core S T).mp hp
  obtain ⟨-, hq2⟩ := (mem_hstrip S T r).mp hq
  rw [hq2]
  exact T.not_conflict_core_epO hpI hpP _ hr

lemma not_conflict_core_vstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂)
    {t : V₁} (ht : t ∈ S.ports) {p q : V₁ × V₂}
    (hp : p ∈ core S T) (hq : q ∈ vstrip S T t) : ¬ conflict G₁ p.1 q.1 := by
  obtain ⟨⟨hpI, hpP⟩, -⟩ := (mem_core S T).mp hp
  obtain ⟨-, hq1⟩ := (mem_vstrip S T t).mp hq
  rw [hq1]
  exact S.not_conflict_core_epO hpI hpP _ ht

lemma not_conflict_hstrip_same (S : RichPortSystem G₁) (T : RichPortSystem G₂)
    {r : V₂} {p q : V₁ × V₂} (hp : p ∈ hstrip S T r) (hq : q ∈ hstrip S T r)
    (hne : p ≠ q) : ¬ conflict G₁ p.1 q.1 := by
  obtain ⟨hpX, hp2⟩ := (mem_hstrip S T r).mp hp
  obtain ⟨hqX, hq2⟩ := (mem_hstrip S T r).mp hq
  refine not_conflict_of_indep S.hX hpX hqX ?_
  intro h1
  exact hne (Prod.ext h1 (by rw [hp2, hq2, h1]))

lemma not_conflict_vstrip_same (S : RichPortSystem G₁) (T : RichPortSystem G₂)
    {t : V₁} {p q : V₁ × V₂} (hp : p ∈ vstrip S T t) (hq : q ∈ vstrip S T t)
    (hne : p ≠ q) : ¬ conflict G₂ p.2 q.2 := by
  obtain ⟨hpX, hp1⟩ := (mem_vstrip S T t).mp hp
  obtain ⟨hqX, hq1⟩ := (mem_vstrip S T t).mp hq
  refine not_conflict_of_indep T.hX hpX hqX ?_
  intro h2
  exact hne (Prod.ext (by rw [hp1, hq1, h2]) h2)

lemma not_conflict_hstrip_hstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂)
    {r s : V₂} (hr : r ∈ T.ports) (hs : s ∈ T.ports) (hrs : r ≠ s) {p q : V₁ × V₂}
    (hp : p ∈ hstrip S T r) (hq : q ∈ hstrip S T s) :
    ¬ conflict G₁ p.1 q.1 ∨ ¬ conflict G₂ p.2 q.2 := by
  obtain ⟨hpX, hp2⟩ := (mem_hstrip S T r).mp hp
  obtain ⟨hqX, hq2⟩ := (mem_hstrip S T s).mp hq
  by_cases h1 : p.1 = q.1
  · right
    rw [hp2, hq2, ← h1]
    exact T.not_conflict_epO_epO _ hr hs hrs
  · left
    exact not_conflict_of_indep S.hX hpX hqX h1

lemma not_conflict_vstrip_vstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂)
    {t u : V₁} (ht : t ∈ S.ports) (hu : u ∈ S.ports) (htu : t ≠ u) {p q : V₁ × V₂}
    (hp : p ∈ vstrip S T t) (hq : q ∈ vstrip S T u) :
    ¬ conflict G₁ p.1 q.1 ∨ ¬ conflict G₂ p.2 q.2 := by
  obtain ⟨hpX, hp1⟩ := (mem_vstrip S T t).mp hp
  obtain ⟨hqX, hq1⟩ := (mem_vstrip S T u).mp hq
  by_cases h2 : p.2 = q.2
  · left
    rw [hp1, hq1, ← h2]
    exact S.not_conflict_epO_epO _ ht hu htu
  · right
    exact not_conflict_of_indep T.hX hpX hqX h2

/-- **The crux.**  A horizontal and a vertical strip word are never
confusable: the class of `x` fixes the side used in coordinate 2, the class of `y`
fixes the *opposite* side in coordinate 1, and the two demands contradict. -/
lemma not_conflict_hstrip_vstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂)
    {r : V₂} (hr : r ∈ T.ports) {t : V₁} (ht : t ∈ S.ports) {p q : V₁ × V₂}
    (hp : p ∈ hstrip S T r) (hq : q ∈ vstrip S T t) :
    ¬ conflict G₁ p.1 q.1 ∨ ¬ conflict G₂ p.2 q.2 := by
  obtain ⟨hpX, hp2⟩ := (mem_hstrip S T r).mp hp
  obtain ⟨hqX, hq1⟩ := (mem_vstrip S T t).mp hq
  by_cases hc1 : conflict G₁ p.1 q.1
  · right
    intro hc2
    have hy : q.2 ∈ T.Xc ((S.cls p.1).getD (T.side r)) := by
      refine T.mem_Xc_of_conflict_epO hqX (o := S.cls p.1) hr ?_
      rw [← hp2]
      exact conflict_symm hc2
    have hclsy : T.cls q.2 = some ((S.cls p.1).getD (T.side r)) :=
      T.cls_eq_some_of_mem_Xc hy
    have hx : p.1 ∈ S.Xc (((T.cls q.2).map Bool.not).getD (S.side t)) := by
      refine S.mem_Xc_of_conflict_epO hpX (o := (T.cls q.2).map Bool.not) ht ?_
      rw [← hq1]
      exact hc1
    have hclsx : S.cls p.1 = some (((T.cls q.2).map Bool.not).getD (S.side t)) :=
      S.cls_eq_some_of_mem_Xc hx
    rw [hclsy, Option.map_some, Option.getD_some] at hclsx
    cases hA : S.cls p.1 with
    | none => rw [hA] at hclsx; simp at hclsx
    | some b => rw [hA] at hclsx; simp at hclsx
  · left
    exact hc1

/-- **Independence of the lifted set — unconditional.** -/
theorem isIndepSet_liftSet (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (strongProd G₁ G₂).IsIndepSet ↑(liftSet S T) := by
  intro p hp q hq hne
  rw [Finset.mem_coe, mem_liftSet] at hp hq
  rcases hp with hp | ⟨s₁, hs₁, hp⟩ | ⟨t₁, ht₁, hp⟩ <;>
    rcases hq with hq | ⟨s₂, hs₂, hq⟩ | ⟨t₂, ht₂, hq⟩
  · refine not_adj_strongProd p q ?_
    by_cases h1 : p.1 = q.1
    · right
      refine not_conflict_of_indep T.hI ((mem_core S T).mp hp).2.1
        ((mem_core S T).mp hq).2.1 ?_
      intro h2
      exact hne (Prod.ext h1 h2)
    · left
      exact not_conflict_of_indep S.hI ((mem_core S T).mp hp).1.1
        ((mem_core S T).mp hq).1.1 h1
  · exact not_adj_strongProd p q (Or.inr (not_conflict_core_hstrip S T hs₂ hp hq))
  · exact not_adj_strongProd p q (Or.inl (not_conflict_core_vstrip S T ht₂ hp hq))
  · exact not_adj_strongProd p q
      (Or.inr fun hc => not_conflict_core_hstrip S T hs₁ hq hp (conflict_symm hc))
  · by_cases hss : s₁ = s₂
    · subst hss
      exact not_adj_strongProd p q (Or.inl (not_conflict_hstrip_same S T hp hq hne))
    · exact not_adj_strongProd p q (not_conflict_hstrip_hstrip S T hs₁ hs₂ hss hp hq)
  · exact not_adj_strongProd p q (not_conflict_hstrip_vstrip S T hs₁ ht₂ hp hq)
  · exact not_adj_strongProd p q
      (Or.inl fun hc => not_conflict_core_vstrip S T ht₁ hq hp (conflict_symm hc))
  · refine not_adj_strongProd p q ?_
    rcases not_conflict_hstrip_vstrip S T hs₂ ht₁ hq hp with h | h
    · left; exact fun hc => h (conflict_symm hc)
    · right; exact fun hc => h (conflict_symm hc)
  · by_cases htt : t₁ = t₂
    · subst htt
      exact not_adj_strongProd p q (Or.inr (not_conflict_vstrip_same S T hp hq hne))
    · exact not_adj_strongProd p q (not_conflict_vstrip_vstrip S T ht₁ ht₂ htt hp hq)

/-! ### The lifted auxiliary code: `L' = L * K` -/

def liftX (S : RichPortSystem G₁) (T : RichPortSystem G₂) : Finset (V₁ × V₂) := S.X ×ˢ T.X

omit [DecidableEq V₂] in
theorem isIndepSet_liftX (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (strongProd G₁ G₂).IsIndepSet ↑(liftX S T) := by
  intro p hp q hq hne
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hq)
  refine not_adj_strongProd p q ?_
  by_cases h1 : p.1 = q.1
  · right
    refine not_conflict_of_indep T.hX hp2 hq2 ?_
    intro h2
    exact hne (Prod.ext h1 h2)
  · left
    exact not_conflict_of_indep S.hX hp1 hq1 h1

omit [DecidableEq V₁] [DecidableEq V₂] in
/-- **`L' = L * K`.** -/
theorem card_liftX (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftX S T).card = S.L * T.L := by
  rw [liftX, Finset.card_product]
  rfl

/-! ### The lifted pairs -/

/-- The lifted parents. -/
def liftPorts (S : RichPortSystem G₁) (T : RichPortSystem G₂) : Finset (V₁ × V₂) :=
  (S.Xstar ×ˢ T.ports) ∪ (S.ports ×ˢ T.Xstar)

/-- The lifted endpoint function. -/
def liftEp (S : RichPortSystem G₁) (T : RichPortSystem G₂) (c : Bool) (u : V₁ × V₂) :
    V₁ × V₂ := if u.1 ∈ S.ports then (S.ep c u.1, u.2) else (u.1, T.ep c u.2)

/-- The lifted side function. -/
def liftSide (S : RichPortSystem G₁) (T : RichPortSystem G₂) (u : V₁ × V₂) : Bool :=
  if u.1 ∈ S.ports then S.side u.1 else T.side u.2

lemma mem_liftPorts (S : RichPortSystem G₁) (T : RichPortSystem G₂) {p : V₁ × V₂} :
    p ∈ liftPorts S T ↔
      (p.1 ∈ S.Xstar ∧ p.2 ∈ T.ports) ∨ (p.1 ∈ S.ports ∧ p.2 ∈ T.Xstar) := by
  rw [liftPorts, Finset.mem_union, Finset.mem_product, Finset.mem_product]

omit [DecidableEq V₂] in
lemma liftEp_hport (S : RichPortSystem G₁) (T : RichPortSystem G₂) {p : V₁ × V₂}
    (h : p.1 ∈ S.Xstar) (c : Bool) : liftEp S T c p = (p.1, T.ep c p.2) := by
  rw [liftEp, if_neg (S.notMem_ports_of_mem_Xstar h)]

omit [DecidableEq V₂] in
lemma liftEp_vport (S : RichPortSystem G₁) (T : RichPortSystem G₂) {p : V₁ × V₂}
    (h : p.1 ∈ S.ports) (c : Bool) : liftEp S T c p = (S.ep c p.1, p.2) := by
  rw [liftEp, if_pos h]

omit [DecidableEq V₂] in
lemma liftSide_hport (S : RichPortSystem G₁) (T : RichPortSystem G₂) {p : V₁ × V₂}
    (h : p.1 ∈ S.Xstar) : liftSide S T p = T.side p.2 := by
  rw [liftSide, if_neg (S.notMem_ports_of_mem_Xstar h)]

omit [DecidableEq V₂] in
lemma liftSide_vport (S : RichPortSystem G₁) (T : RichPortSystem G₂) {p : V₁ × V₂}
    (h : p.1 ∈ S.ports) : liftSide S T p = S.side p.1 := by
  rw [liftSide, if_pos h]

lemma disjoint_liftPorts_parts (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    Disjoint (S.Xstar ×ˢ T.ports) (S.ports ×ˢ T.Xstar) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  exact S.notMem_ports_of_mem_Xstar (Finset.mem_product.mp hp).1
    (Finset.mem_product.mp hq).1

/-- **`d' = eta*e + d*zeta`.** -/
theorem card_liftPorts (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftPorts S T).card = S.eta * T.d + S.d * T.eta := by
  rw [liftPorts, Finset.card_union_of_disjoint (disjoint_liftPorts_parts S T),
    Finset.card_product, Finset.card_product]
  rfl

/-! ### The lifted footprints and neutral part -/

def liftNeutral (S : RichPortSystem G₁) (T : RichPortSystem G₂) : Finset (V₁ × V₂) :=
  (S.Xstar ×ˢ T.Xstar) ∪ ((S.X \ S.Xstar) ×ˢ (T.X \ T.Xstar))

lemma liftNeutral_subset_liftX (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    liftNeutral S T ⊆ liftX S T := by
  intro p hp
  rw [liftX, Finset.mem_product]
  rcases Finset.mem_union.mp hp with h | h
  · obtain ⟨h1, h2⟩ := Finset.mem_product.mp h
    exact ⟨S.Xstar_subset_X h1, T.Xstar_subset_X h2⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_product.mp h
    exact ⟨(Finset.mem_sdiff.mp h1).1, (Finset.mem_sdiff.mp h2).1⟩

/-- **`eta' = eta*zeta + (L-eta)*(K-zeta)`.** -/
theorem card_liftNeutral (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftNeutral S T).card = S.eta * T.eta + (S.L - S.eta) * (T.L - T.eta) := by
  have hdisj : Disjoint (S.Xstar ×ˢ T.Xstar) ((S.X \ S.Xstar) ×ˢ (T.X \ T.Xstar)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact (Finset.mem_sdiff.mp (Finset.mem_product.mp hq).1).2 (Finset.mem_product.mp hp).1
  rw [liftNeutral, Finset.card_union_of_disjoint hdisj, Finset.card_product,
    Finset.card_product, Finset.card_sdiff_of_subset S.Xstar_subset_X,
    Finset.card_sdiff_of_subset T.Xstar_subset_X]
  rfl

/-- **The lifted footprint classes.** -/
theorem exists_liftEp_conflict_iff (S : RichPortSystem G₁) (T : RichPortSystem G₂)
    {u : V₁ × V₂} (hu : u ∈ liftX S T) (c : Bool) :
    (∃ p ∈ liftPorts S T, conflict (strongProd G₁ G₂) u (liftEp S T c p)) ↔
      (u.1 ∈ S.Xstar ∧ u.2 ∈ T.Xc c) ∨ (u.1 ∈ S.Xc c ∧ u.2 ∈ T.Xstar) := by
  obtain ⟨huX1, huX2⟩ := Finset.mem_product.mp hu
  constructor
  · rintro ⟨p, hp, hconf⟩
    rcases (mem_liftPorts S T).mp hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    · rw [liftEp_hport S T hp1] at hconf
      left
      have hcf := conflict_fst hconf
      have hcs := conflict_snd hconf
      have h1 : u.1 = p.1 :=
        eq_of_conflict_of_indep S.hX huX1 (S.Xstar_subset_X hp1) hcf
      exact ⟨by rw [h1]; exact hp1, T.mem_Xc_of_conflict huX2 hp2 hcs⟩
    · rw [liftEp_vport S T hp1] at hconf
      right
      have hcf := conflict_fst hconf
      have hcs := conflict_snd hconf
      have h2 : u.2 = p.2 :=
        eq_of_conflict_of_indep T.hX huX2 (T.Xstar_subset_X hp2) hcs
      exact ⟨S.mem_Xc_of_conflict huX1 hp1 hcf, by rw [h2]; exact hp2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · obtain ⟨-, r, hr, hcr⟩ := T.mem_Xc.mp h2
      refine ⟨(u.1, r), (mem_liftPorts S T).mpr (Or.inl ⟨h1, hr⟩), ?_⟩
      rw [liftEp_hport S T (show ((u.1, r) : V₁ × V₂).1 ∈ S.Xstar from h1)]
      exact conflict_strongProd_iff.mpr ⟨conflict_rfl u.1, hcr⟩
    · obtain ⟨-, t, ht, hct⟩ := S.mem_Xc.mp h1
      refine ⟨(t, u.2), (mem_liftPorts S T).mpr (Or.inr ⟨ht, h2⟩), ?_⟩
      rw [liftEp_vport S T (show ((t, u.2) : V₁ × V₂).1 ∈ S.ports from ht)]
      exact conflict_strongProd_iff.mpr ⟨hct, conflict_rfl u.2⟩

lemma mem_liftNeutral_iff_iff (S : RichPortSystem G₁) (T : RichPortSystem G₂)
    {u : V₁ × V₂} (hu : u ∈ liftX S T) :
    u ∈ liftNeutral S T ↔ (u.1 ∈ S.Xstar ↔ u.2 ∈ T.Xstar) := by
  obtain ⟨huX1, huX2⟩ := Finset.mem_product.mp hu
  rw [liftNeutral, Finset.mem_union, Finset.mem_product, Finset.mem_product,
    Finset.mem_sdiff, Finset.mem_sdiff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨⟨-, h1⟩, ⟨-, h2⟩⟩)
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  · intro h
    by_cases h1 : u.1 ∈ S.Xstar
    · exact Or.inl ⟨h1, h.mp h1⟩
    · exact Or.inr ⟨⟨huX1, h1⟩, ⟨huX2, fun h2 => h1 (h.mpr h2)⟩⟩

/-- **The neutrality characterisation.** -/
theorem mem_liftNeutral_iff (S : RichPortSystem G₁) (T : RichPortSystem G₂)
    {u : V₁ × V₂} (hu : u ∈ liftX S T) :
    u ∈ liftNeutral S T ↔
      ∀ c : Bool, ∀ p ∈ liftPorts S T,
        ¬ conflict (strongProd G₁ G₂) u (liftEp S T c p) := by
  obtain ⟨huX1, huX2⟩ := Finset.mem_product.mp hu
  rw [mem_liftNeutral_iff_iff S T hu]
  constructor
  · intro h c p hp hconf
    have hcase := (exists_liftEp_conflict_iff S T hu c).mp ⟨p, hp, hconf⟩
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases (T.mem_Xstar.mp (h.mp h1)) with ⟨-, hn0, hn1⟩
      cases c
      · exact hn0 h2
      · exact hn1 h2
    · rcases (S.mem_Xstar.mp (h.mpr h2)) with ⟨-, hn0, hn1⟩
      cases c
      · exact hn0 h1
      · exact hn1 h1
  · intro h
    have hno : ∀ c : Bool, ¬ ((u.1 ∈ S.Xstar ∧ u.2 ∈ T.Xc c) ∨
        (u.1 ∈ S.Xc c ∧ u.2 ∈ T.Xstar)) := by
      intro c hcase
      obtain ⟨p, hp, hconf⟩ := (exists_liftEp_conflict_iff S T hu c).mpr hcase
      exact h c p hp hconf
    constructor
    · intro h1
      exact T.mem_Xstar.mpr ⟨huX2, fun hc => hno false (Or.inl ⟨h1, hc⟩),
        fun hc => hno true (Or.inl ⟨h1, hc⟩)⟩
    · intro h2
      exact S.mem_Xstar.mpr ⟨huX1, fun hc => hno false (Or.inr ⟨hc, h2⟩),
        fun hc => hno true (Or.inr ⟨hc, h2⟩)⟩

/-! ### The lifted data really is a rich port system -/

lemma liftPorts_subset_liftSet (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    liftPorts S T ⊆ liftSet S T := by
  intro p hp
  rw [mem_liftSet]
  rcases (mem_liftPorts S T).mp hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · refine Or.inr (Or.inl ⟨p.2, hp2, ?_⟩)
    rw [mem_hstrip, S.cls_eq_none_of_mem_Xstar hp1]
    exact ⟨S.Xstar_subset_X hp1, rfl⟩
  · refine Or.inr (Or.inr ⟨p.1, hp1, ?_⟩)
    rw [mem_vstrip, T.cls_eq_none_of_mem_Xstar hp2]
    exact ⟨T.Xstar_subset_X hp2, rfl⟩

lemma liftEp_parent (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    ∀ p ∈ liftPorts S T, liftEp S T (liftSide S T p) p = p := by
  intro p hp
  rcases (mem_liftPorts S T).mp hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · rw [liftSide_hport S T hp1, liftEp_hport S T hp1]
    exact Prod.ext rfl (T.hep_parent p.2 hp2)
  · rw [liftSide_vport S T hp1, liftEp_vport S T hp1]
    exact Prod.ext (S.hep_parent p.1 hp1) rfl

omit [DecidableEq V₂] in
lemma liftAlt_hport (S : RichPortSystem G₁) (T : RichPortSystem G₂) {p : V₁ × V₂}
    (h : p.1 ∈ S.Xstar) :
    liftEp S T (!liftSide S T p) p = (p.1, T.alt p.2) := by
  rw [liftSide_hport S T h, liftEp_hport S T h]
  rfl

omit [DecidableEq V₂] in
lemma liftAlt_vport (S : RichPortSystem G₁) (T : RichPortSystem G₂) {p : V₁ × V₂}
    (h : p.1 ∈ S.ports) :
    liftEp S T (!liftSide S T p) p = (S.alt p.1, p.2) := by
  rw [liftSide_vport S T h, liftEp_vport S T h]
  rfl

lemma liftAlt_notMem_liftSet (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    ∀ p ∈ liftPorts S T, liftEp S T (!liftSide S T p) p ∉ liftSet S T := by
  intro p hp hmem
  rw [mem_liftSet] at hmem
  rcases (mem_liftPorts S T).mp hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · rw [liftAlt_hport S T hp1] at hmem
    rcases hmem with h | ⟨s, hs, h⟩ | ⟨t, ht, h⟩
    · exact T.alt_notMem_I hp2 ((mem_core_mk S T).mp h).2.1
    · obtain ⟨-, h2⟩ := (mem_hstrip_mk S T s).mp h
      rw [S.cls_eq_none_of_mem_Xstar hp1] at h2
      exact T.alt_notMem_I hp2 (by rw [h2]; exact T.hports hs)
    · obtain ⟨-, h1⟩ := (mem_vstrip_mk S T t).mp h
      exact S.not_conflict_epO_of_mem_Xstar hp1 _ ht (Or.inl h1)
  · rw [liftAlt_vport S T hp1] at hmem
    rcases hmem with h | ⟨s, hs, h⟩ | ⟨t, ht, h⟩
    · exact S.alt_notMem_I hp1 ((mem_core_mk S T).mp h).1.1
    · obtain ⟨-, h2⟩ := (mem_hstrip_mk S T s).mp h
      exact T.not_conflict_epO_of_mem_Xstar hp2 _ hs (Or.inl h2)
    · obtain ⟨-, h1⟩ := (mem_vstrip_mk S T t).mp h
      rw [T.cls_eq_none_of_mem_Xstar hp2] at h1
      exact S.alt_notMem_I hp1 (by rw [h1]; exact S.hports ht)

lemma liftAlt_private (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    ∀ p ∈ liftPorts S T, ∀ w ∈ liftSet S T,
      conflict (strongProd G₁ G₂) (liftEp S T (!liftSide S T p) p) w → w = p := by
  intro p hp w hw hconf
  rw [mem_liftSet] at hw
  rcases (mem_liftPorts S T).mp hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · rw [liftAlt_hport S T hp1] at hconf
    have hcf := conflict_fst hconf
    have hcs := conflict_snd hconf
    rcases hw with h | ⟨s, hs, h⟩ | ⟨t, ht, h⟩
    · exfalso
      obtain ⟨-, hwI, hwP⟩ := (mem_core S T).mp h
      exact hwP (by rw [T.hprivate p.2 hp2 w.2 hwI hcs]; exact hp2)
    · obtain ⟨hwX, h2⟩ := (mem_hstrip S T s).mp h
      have hw1 : w.1 = p.1 :=
        (eq_of_conflict_of_indep S.hX (S.Xstar_subset_X hp1) hwX hcf).symm
      rw [hw1, S.cls_eq_none_of_mem_Xstar hp1] at h2
      rw [h2] at hcs
      have hsp : s = p.2 := T.hprivate p.2 hp2 s (T.hports hs) hcs
      exact Prod.ext hw1 (by rw [h2, hsp, T.epO_none])
    · exfalso
      obtain ⟨-, h1⟩ := (mem_vstrip S T t).mp h
      rw [h1] at hcf
      exact S.not_conflict_epO_of_mem_Xstar hp1 _ ht hcf
  · rw [liftAlt_vport S T hp1] at hconf
    have hcf := conflict_fst hconf
    have hcs := conflict_snd hconf
    rcases hw with h | ⟨s, hs, h⟩ | ⟨t, ht, h⟩
    · exfalso
      obtain ⟨⟨hwI, hwP⟩, -⟩ := (mem_core S T).mp h
      exact hwP (by rw [S.hprivate p.1 hp1 w.1 hwI hcf]; exact hp1)
    · exfalso
      obtain ⟨-, h2⟩ := (mem_hstrip S T s).mp h
      rw [h2] at hcs
      exact T.not_conflict_epO_of_mem_Xstar hp2 _ hs hcs
    · obtain ⟨hwX, h1⟩ := (mem_vstrip S T t).mp h
      have hw2 : w.2 = p.2 :=
        (eq_of_conflict_of_indep T.hX (T.Xstar_subset_X hp2) hwX hcs).symm
      rw [hw2, T.cls_eq_none_of_mem_Xstar hp2] at h1
      rw [h1] at hcf
      have htp : t = p.1 := S.hprivate p.1 hp1 t (S.hports ht) hcf
      exact Prod.ext (by rw [h1, htp]; rfl) hw2

/-- **The lifted pairs are edges too.**  A lifted horizontal port is `(x, r)` with `x`
neutral and `r` a `T`-port; its alternative is `(x, alt r)`.  Conflict in a strong product
is conflict in every coordinate: `x` conflicts with itself, and `r` conflicts with `alt r`
by `hep_conflict` on the base.  Vertical ports are symmetric. -/
lemma liftEp_conflict (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    ∀ p ∈ liftPorts S T,
      conflict (strongProd G₁ G₂) p (liftEp S T (!liftSide S T p) p) := by
  intro p hp
  rcases (mem_liftPorts S T).mp hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · rw [liftAlt_hport S T hp1]
    refine conflict_strongProd_iff.mpr ⟨conflict_rfl p.1, ?_⟩
    exact T.hep_conflict p.2 hp2
  · rw [liftAlt_vport S T hp1]
    refine conflict_strongProd_iff.mpr ⟨?_, conflict_rfl p.2⟩
    exact S.hep_conflict p.1 hp1

lemma liftAlt_inj (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    ∀ p ∈ liftPorts S T, ∀ q ∈ liftPorts S T,
      liftEp S T (!liftSide S T p) p = liftEp S T (!liftSide S T q) q → p = q := by
  intro p hp q hq h
  rcases (mem_liftPorts S T).mp hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;>
    rcases (mem_liftPorts S T).mp hq with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
  · rw [liftAlt_hport S T hp1, liftAlt_hport S T hq1, Prod.mk.injEq] at h
    exact Prod.ext h.1 (T.halt_inj p.2 hp2 q.2 hq2 h.2)
  · rw [liftAlt_hport S T hp1, liftAlt_vport S T hq1, Prod.mk.injEq] at h
    exact absurd (Or.inl h.2.symm : conflict G₂ q.2 (T.alt p.2))
      (T.not_conflict_ep_of_mem_Xstar hq2 (!T.side p.2) hp2)
  · rw [liftAlt_vport S T hp1, liftAlt_hport S T hq1, Prod.mk.injEq] at h
    exact absurd (Or.inl h.2 : conflict G₂ p.2 (T.alt q.2))
      (T.not_conflict_ep_of_mem_Xstar hp2 (!T.side q.2) hq2)
  · rw [liftAlt_vport S T hp1, liftAlt_vport S T hq1, Prod.mk.injEq] at h
    exact Prod.ext (S.halt_inj p.1 hp1 q.1 hq1 h.1) h.2

lemma liftP_indep (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    ∀ c : Bool, ∀ p ∈ liftPorts S T, ∀ q ∈ liftPorts S T, p ≠ q →
      ¬ conflict (strongProd G₁ G₂) (liftEp S T c p) (liftEp S T c q) := by
  intro c p hp q hq hne hconf
  rcases (mem_liftPorts S T).mp hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;>
    rcases (mem_liftPorts S T).mp hq with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
  · rw [liftEp_hport S T hp1, liftEp_hport S T hq1] at hconf
    have hcf := conflict_fst hconf
    have hcs := conflict_snd hconf
    by_cases h1 : p.1 = q.1
    · exact T.hP_indep c p.2 hp2 q.2 hq2 (fun h2 => hne (Prod.ext h1 h2)) hcs
    · exact not_conflict_of_indep S.hX (S.Xstar_subset_X hp1) (S.Xstar_subset_X hq1) h1 hcf
  · rw [liftEp_hport S T hp1, liftEp_vport S T hq1] at hconf
    exact S.not_conflict_ep_of_mem_Xstar hp1 c hq1 (conflict_fst hconf)
  · rw [liftEp_vport S T hp1, liftEp_hport S T hq1] at hconf
    exact S.not_conflict_ep_of_mem_Xstar hq1 c hp1 (conflict_symm (conflict_fst hconf))
  · rw [liftEp_vport S T hp1, liftEp_vport S T hq1] at hconf
    have hcf := conflict_fst hconf
    have hcs := conflict_snd hconf
    by_cases h2 : p.2 = q.2
    · exact S.hP_indep c p.1 hp1 q.1 hq1 (fun h1 => hne (Prod.ext h1 h2)) hcf
    · exact not_conflict_of_indep T.hX (T.Xstar_subset_X hp2) (T.Xstar_subset_X hq2) h2 hcs

lemma liftSep (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    ∀ u ∈ liftX S T,
      ¬ ((∃ p ∈ liftPorts S T, conflict (strongProd G₁ G₂) u (liftEp S T false p)) ∧
         (∃ p ∈ liftPorts S T, conflict (strongProd G₁ G₂) u (liftEp S T true p))) := by
  rintro u hu ⟨h0, h1⟩
  have e0 := (exists_liftEp_conflict_iff S T hu false).mp h0
  have e1 := (exists_liftEp_conflict_iff S T hu true).mp h1
  rcases e0 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases e1 with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · exact Finset.disjoint_left.mp T.Xc_disjoint hb hd
  · exact (S.mem_Xstar.mp ha).2.2 hc
  · exact (S.mem_Xstar.mp hc).2.1 ha
  · exact Finset.disjoint_left.mp S.Xc_disjoint ha hc

/-- **The lifted rich port system.**  The lift of two rich port systems is again a
rich port system. -/
def liftRPS (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    RichPortSystem (strongProd G₁ G₂) where
  I := liftSet S T
  hI := isIndepSet_liftSet S T
  ports := liftPorts S T
  hports := liftPorts_subset_liftSet S T
  ep := liftEp S T
  side := liftSide S T
  hep_parent := liftEp_parent S T
  halt_not := liftAlt_notMem_liftSet S T
  hprivate := liftAlt_private S T
  hep_conflict := liftEp_conflict S T
  halt_inj := liftAlt_inj S T
  hP_indep := liftP_indep S T
  X := liftX S T
  hX := isIndepSet_liftX S T
  hsep := liftSep S T

@[simp] lemma liftRPS_I (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftRPS S T).I = liftSet S T := rfl

@[simp] lemma liftRPS_ports (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftRPS S T).ports = liftPorts S T := rfl

@[simp] lemma liftRPS_X (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftRPS S T).X = liftX S T := rfl

@[simp] lemma liftRPS_ep (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftRPS S T).ep = liftEp S T := rfl

theorem liftRPS_Xstar (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftRPS S T).Xstar = liftNeutral S T := by
  ext u
  rw [RichPortSystem.mem_Xstar]
  constructor
  · rintro ⟨hu, h0, h1⟩
    refine (mem_liftNeutral_iff S T hu).mpr ?_
    intro c p hp hconf
    cases c
    · exact h0 (((liftRPS S T).mem_Xc).mpr ⟨hu, p, hp, hconf⟩)
    · exact h1 (((liftRPS S T).mem_Xc).mpr ⟨hu, p, hp, hconf⟩)
  · intro hun
    have hu : u ∈ liftX S T := liftNeutral_subset_liftX S T hun
    have h := (mem_liftNeutral_iff S T hu).mp hun
    refine ⟨hu, ?_, ?_⟩
    · intro hcx
      obtain ⟨-, p, hp, hcp⟩ := ((liftRPS S T).mem_Xc).mp hcx
      exact h false p hp hcp
    · intro hcx
      obtain ⟨-, p, hp, hcp⟩ := ((liftRPS S T).mem_Xc).mp hcx
      exact h true p hp hcp

/-- **`d' = eta*e + d*zeta`.** -/
theorem liftRPS_d (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftRPS S T).d = S.eta * T.d + S.d * T.eta := card_liftPorts S T

/-- **`L' = L*K`.** -/
theorem liftRPS_L (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftRPS S T).L = S.L * T.L := card_liftX S T

/-- **`eta' = eta*zeta + (L-eta)*(K-zeta)`.** -/
theorem liftRPS_eta (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftRPS S T).eta = S.eta * T.eta + (S.L - S.eta) * (T.L - T.eta) := by
  show (liftRPS S T).Xstar.card = _
  rw [liftRPS_Xstar]
  exact card_liftNeutral S T

/-! ### The size of the lifted set -/

omit [DecidableEq V₁] [DecidableEq V₂] in
lemma disjoint_of_not_conflict_fst {A B : Finset (V₁ × V₂)}
    (h : ∀ p ∈ A, ∀ q ∈ B, ¬ conflict G₁ p.1 q.1) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro a ha hb
  exact h a ha a hb (conflict_rfl a.1)

omit [DecidableEq V₁] [DecidableEq V₂] in
lemma disjoint_of_not_conflict_snd {A B : Finset (V₁ × V₂)}
    (h : ∀ p ∈ A, ∀ q ∈ B, ¬ conflict G₂ p.2 q.2) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro a ha hb
  exact h a ha a hb (conflict_rfl a.2)

omit [DecidableEq V₁] [DecidableEq V₂] in
lemma disjoint_of_not_conflict {A B : Finset (V₁ × V₂)}
    (h : ∀ p ∈ A, ∀ q ∈ B, ¬ conflict G₁ p.1 q.1 ∨ ¬ conflict G₂ p.2 q.2) :
    Disjoint A B := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rcases h a ha a hb with hc | hc
  · exact hc (conflict_rfl a.1)
  · exact hc (conflict_rfl a.2)

lemma card_core (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (core S T).card = (S.N - S.d) * (T.N - T.d) := by
  rw [core, Finset.card_product, Finset.card_sdiff_of_subset S.hports,
    Finset.card_sdiff_of_subset T.hports]
  rfl

lemma card_hstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂) (r : V₂) :
    (hstrip S T r).card = S.L := by
  rw [hstrip, Finset.card_image_of_injective _
    (fun a b hab => by simpa using congrArg Prod.fst hab)]
  rfl

lemma card_vstrip (S : RichPortSystem G₁) (T : RichPortSystem G₂) (t : V₁) :
    (vstrip S T t).card = T.L := by
  rw [vstrip, Finset.card_image_of_injective _
    (fun a b hab => by simpa using congrArg Prod.snd hab)]
  rfl

lemma card_hstrips (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (T.ports.biUnion (hstrip S T)).card = T.d * S.L := by
  have hdisj : ∀ r ∈ T.ports, ∀ s ∈ T.ports, r ≠ s →
      Disjoint (hstrip S T r) (hstrip S T s) := fun r hr s hs hrs =>
    disjoint_of_not_conflict fun p hp q hq => not_conflict_hstrip_hstrip S T hr hs hrs hp hq
  rw [Finset.card_biUnion hdisj,
    Finset.sum_congr rfl (fun r _ => card_hstrip S T r), Finset.sum_const, smul_eq_mul]
  rfl

lemma card_vstrips (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (S.ports.biUnion (vstrip S T)).card = S.d * T.L := by
  have hdisj : ∀ t ∈ S.ports, ∀ u ∈ S.ports, t ≠ u →
      Disjoint (vstrip S T t) (vstrip S T u) := fun t ht u hu htu =>
    disjoint_of_not_conflict fun p hp q hq => not_conflict_vstrip_vstrip S T ht hu htu hp hq
  rw [Finset.card_biUnion hdisj,
    Finset.sum_congr rfl (fun t _ => card_vstrip S T t), Finset.sum_const, smul_eq_mul]
  rfl

/-- **`N' = (N-d)*(M-e) + L*e + d*K`.** -/
theorem card_liftSet (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftSet S T).card = (S.N - S.d) * (T.N - T.d) + S.L * T.d + S.d * T.L := by
  have hch : Disjoint (core S T) (T.ports.biUnion (hstrip S T)) := by
    rw [Finset.disjoint_biUnion_right]
    intro r hr
    exact disjoint_of_not_conflict_snd fun p hp q hq => not_conflict_core_hstrip S T hr hp hq
  have hcv : Disjoint (core S T) (S.ports.biUnion (vstrip S T)) := by
    rw [Finset.disjoint_biUnion_right]
    intro t ht
    exact disjoint_of_not_conflict_fst fun p hp q hq => not_conflict_core_vstrip S T ht hp hq
  have hhv : Disjoint (T.ports.biUnion (hstrip S T)) (S.ports.biUnion (vstrip S T)) := by
    rw [Finset.disjoint_biUnion_left]
    intro r hr
    rw [Finset.disjoint_biUnion_right]
    intro t ht
    exact disjoint_of_not_conflict fun p hp q hq => not_conflict_hstrip_vstrip S T hr ht hp hq
  rw [liftSet, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hcv, hhv⟩),
    Finset.card_union_of_disjoint hch, card_core, card_hstrips, card_vstrips,
    Nat.mul_comm T.d S.L]

/-- **`N' = liftRPS.N`.** -/
theorem liftRPS_N (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    (liftRPS S T).N = (S.N - S.d) * (T.N - T.d) + S.L * T.d + S.d * T.L :=
  card_liftSet S T

/-- **Closure of the invariant under the lift**, with all four parameters. -/
theorem lift_closure (S : RichPortSystem G₁) (T : RichPortSystem G₂) :
    ∃ P : RichPortSystem (strongProd G₁ G₂),
      P.I = liftSet S T ∧
      P.ports = liftPorts S T ∧
      P.X = liftX S T ∧
      P.Xstar = liftNeutral S T ∧
      P.N = (S.N - S.d) * (T.N - T.d) + S.L * T.d + S.d * T.L ∧
      P.d = S.eta * T.d + S.d * T.eta ∧
      P.L = S.L * T.L ∧
      P.eta = S.eta * T.eta + (S.L - S.eta) * (T.L - T.eta) :=
  ⟨liftRPS S T, rfl, rfl, rfl, liftRPS_Xstar S T, liftRPS_N S T, liftRPS_d S T,
    liftRPS_L S T, liftRPS_eta S T⟩

end Lift

end ShannonBounds
