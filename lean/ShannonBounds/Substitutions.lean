/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.PortRealisation

/-!
# Substitutions over the seven-letter separation system

Admissible substitution tables over the seven-letter separation system of
`PortRealisation.lean`.  Each table is given as a `Letter`-indexed family of words, together
with the proof that it is admissible.
-/

namespace ShannonBounds
namespace Substitutions

open SimpleGraph Letter

set_option maxRecDepth 1000000
set_option exponentiation.threshold 20000
set_option synthInstance.maxSize 4000
set_option synthInstance.maxHeartbeats 4000000

/-! ### Arity 2 -/

/-- An arity-`2` table of `20` words. -/
def T2a : Letter → Finset (Fin 2 → Letter)
  | B =>
      {![B, B], ![H, D], ![V, A], ![D, V], ![A, H]}
  | N =>
      {![N, N], ![A, A], ![A, D], ![D, A], ![D, D]}
  | A =>
      {![A, N], ![N, D]}
  | D =>
      {![D, N], ![N, A]}
  | O =>
      {![O, N], ![N, O]}
  | H =>
      {![H, N], ![N, V]}
  | V =>
      {![V, N], ![N, H]}

/-- `T2a` is admissible. -/
def S2a : Subst Letter Letter.sep 2 :=
  ⟨T2a, by native_decide, by native_decide⟩

/-- An arity-`2` table of `17` words. -/
def T2b : Letter → Finset (Fin 2 → Letter)
  | B =>
      {![A, V], ![B, B], ![D, H]}
  | N =>
      {![A, A], ![N, N]}
  | A =>
      {![A, N], ![B, D], ![D, V], ![V, H]}
  | D =>
      {![D, N], ![N, A]}
  | O =>
      ∅
  | H =>
      {![H, B], ![N, V]}
  | V =>
      {![H, A], ![N, H], ![V, D], ![V, N]}

/-- `T2b` is admissible. -/
def S2b : Subst Letter Letter.sep 2 :=
  ⟨T2b, by native_decide, by native_decide⟩

/-! ### Arity 3 -/

/-- An arity-`3` table of `58` words. -/
def T3a : Letter → Finset (Fin 3 → Letter)
  | B =>
      {![A, H, N], ![A, N, V], ![B, A, H], ![B, B, B], ![B, D, V], ![B, H, D], ![B, V, A],
       ![D, N, H], ![D, V, N], ![H, D, N], ![H, N, A], ![V, A, N], ![V, N, D]}
  | N =>
      {![A, A, N], ![A, D, N], ![A, N, A], ![A, N, D], ![D, A, N], ![D, D, N], ![D, N, A],
       ![D, N, D], ![N, A, A], ![N, A, D], ![N, D, A], ![N, D, D], ![N, N, N]}
  | A =>
      {![A, A, A], ![A, A, D], ![A, D, A], ![A, D, D], ![A, N, N], ![N, A, N], ![N, N, A]}
  | D =>
      {![D, A, A], ![D, A, D], ![D, D, A], ![D, D, D], ![D, N, N], ![N, D, N], ![N, N, D]}
  | O =>
      {![O, A, A], ![O, A, D], ![O, D, A], ![O, D, D]}
  | H =>
      {![H, A, A], ![H, A, D], ![H, D, A], ![H, D, D], ![H, N, N], ![N, H, N], ![N, N, H]}
  | V =>
      {![N, N, V], ![N, V, N], ![V, A, A], ![V, A, D], ![V, D, A], ![V, D, D], ![V, N, N]}

/-- `T3a` is admissible. -/
def S3a : Subst Letter Letter.sep 3 :=
  ⟨T3a, by native_decide, by native_decide⟩

/-- An arity-`3` table of `45` words. -/
def T3b : Letter → Finset (Fin 3 → Letter)
  | B =>
      {![B, B, B], ![B, H, A], ![N, A, V], ![N, D, H], ![N, V, D], ![A, B, H], ![A, H, N],
       ![A, H, D], ![D, B, V], ![D, V, N], ![D, V, D], ![H, N, D], ![H, D, N], ![H, D, D],
       ![V, N, A], ![V, A, B], ![V, D, A]}
  | N =>
      {![B, V, D], ![N, N, N], ![N, V, A], ![A, N, H], ![A, D, H], ![A, H, N], ![D, N, V],
       ![D, D, H], ![D, H, N], ![H, V, D]}
  | A =>
      {![N, B, A], ![N, A, N], ![A, B, B], ![A, A, V], ![A, H, A]}
  | D =>
      {![N, B, D], ![N, D, N], ![D, B, B], ![D, A, V], ![D, H, A]}
  | O =>
      ∅
  | H =>
      {![N, N, H], ![N, H, N], ![H, N, N], ![H, V, V]}
  | V =>
      {![N, N, V], ![N, V, N], ![V, N, N], ![V, V, V]}

/-- `T3b` is admissible. -/
def S3b : Subst Letter Letter.sep 3 :=
  ⟨T3b, by native_decide, by native_decide⟩

/-- An arity-`3` table of `48` words. -/
def T3c : Letter → Finset (Fin 3 → Letter)
  | .B =>
      {![.A, .B, .V], ![.A, .H, .H], ![.A, .V, .A], ![.B, .B, .B], ![.D, .A, .H], ![.D, .H, .A], ![.D, .N, .H], ![.H, .A, .A], ![.H, .A, .N], ![.H, .H, .H], ![.N, .H, .D], ![.N, .V, .A], ![.V, .A, .D], ![.V, .D, .B]}
  | .N =>
      {![.A, .A, .D], ![.A, .D, .A], ![.B, .H, .D], ![.D, .A, .B], ![.D, .B, .H], ![.H, .H, .A], ![.H, .V, .H], ![.N, .N, .N], ![.V, .A, .A], ![.V, .D, .H]}
  | .A =>
      {![.A, .B, .N], ![.A, .N, .D], ![.B, .N, .A], ![.B, .V, .V], ![.H, .D, .N], ![.N, .A, .B], ![.N, .D, .A], ![.V, .N, .V], ![.V, .V, .N]}
  | .D =>
      {![.D, .N, .N], ![.N, .D, .N], ![.N, .N, .D]}
  | .O =>
      ∅
  | .H =>
      {![.B, .H, .N], ![.H, .N, .B], ![.N, .B, .H]}
  | .V =>
      {![.A, .V, .N], ![.D, .H, .N], ![.H, .N, .A], ![.N, .A, .H], ![.N, .D, .V], ![.N, .N, .V], ![.N, .V, .N], ![.V, .N, .D], ![.V, .N, .N]}

/-- `T3c` is admissible. -/
def S3c : Subst Letter Letter.sep 3 := ⟨T3c, by native_decide, by native_decide⟩

/-- An arity-`3` table of `46` words. -/
def T3d : Letter → Finset (Fin 3 → Letter)
  | B =>
      {![A, B, V], ![B, B, B], ![B, H, D], ![B, V, A], ![D, A, H], ![D, D, V], ![D, N, H],
       ![H, A, A], ![H, A, N], ![V, A, D], ![V, D, N], ![V, H, A], ![V, H, H]}
  | N =>
      {![A, A, D], ![B, H, D], ![D, A, B], ![D, B, H], ![H, V, H], ![N, N, N], ![V, A, A],
       ![V, D, H], ![V, H, A]}
  | A =>
      {![A, B, N], ![A, N, D], ![B, D, A], ![B, N, A], ![B, V, V], ![H, D, N], ![N, A, B],
       ![V, N, V], ![V, V, N]}
  | D =>
      {![D, N, N], ![N, D, N], ![N, N, D]}
  | O =>
      ∅
  | H =>
      {![B, H, N], ![H, N, B], ![N, B, H]}
  | V =>
      {![A, V, N], ![D, H, N], ![H, N, A], ![N, A, H], ![N, D, V], ![N, N, V], ![N, V, N],
       ![V, N, D], ![V, N, N]}

/-- `T3d` is admissible. -/
def S3d : Subst Letter Letter.sep 3 :=
  ⟨T3d, by native_decide, by native_decide⟩

/-- An arity-`3` table of `53` words. -/
def T3e : Letter → Finset (Fin 3 → Letter)
  | B =>
      {![A, H, N], ![B, A, H], ![B, B, B], ![B, D, V], ![B, H, D], ![B, V, A], ![D, V, N],
       ![H, D, N], ![H, N, A], ![V, A, N], ![V, N, D]}
  | N =>
      {![A, A, N], ![A, H, N], ![D, A, N], ![D, D, N], ![H, N, A], ![N, A, A], ![N, A, D],
       ![N, D, A], ![N, D, D], ![N, N, N]}
  | A =>
      {![A, A, A], ![A, A, D], ![A, D, A], ![A, D, D], ![A, N, N], ![B, N, A], ![H, N, D],
       ![N, A, N]}
  | D =>
      {![A, N, D], ![D, A, A], ![D, A, D], ![D, D, A], ![D, D, D], ![D, N, N], ![N, D, N],
       ![N, N, D]}
  | O =>
      ∅
  | H =>
      {![B, N, H], ![H, A, A], ![H, A, D], ![H, D, D], ![H, H, A], ![H, N, N], ![N, H, N]}
  | V =>
      {![A, N, V], ![D, N, H], ![N, N, V], ![N, V, N], ![V, A, A], ![V, A, D], ![V, D, A],
       ![V, D, D], ![V, N, N]}

/-- `T3e` is admissible. -/
def S3e : Subst Letter Letter.sep 3 :=
  ⟨T3e, by native_decide, by native_decide⟩

/-- An arity-`3` table of `47` words. -/
def T3f : Letter → Finset (Fin 3 → Letter)
  | B =>
      {![A, H, D], ![A, H, N], ![B, A, H], ![B, B, B], ![B, D, V], ![B, V, A], ![H, D, B],
       ![H, H, H], ![H, N, A], ![N, H, D], ![V, N, D]}
  | N =>
      {![A, H, B], ![B, H, H], ![D, H, A], ![H, D, D], ![H, N, A], ![N, A, A], ![N, A, H],
       ![N, H, A], ![N, N, N], ![V, H, V]}
  | A =>
      {![A, A, A], ![A, A, H], ![A, B, N], ![B, N, A], ![H, H, N], ![H, N, H], ![N, A, N]}
  | D =>
      {![A, N, D], ![D, A, A], ![D, A, D], ![D, B, N], ![N, D, N], ![N, N, D]}
  | O =>
      ∅
  | H =>
      {![B, N, H], ![H, A, B], ![H, A, V], ![H, N, N], ![N, H, N]}
  | V =>
      {![A, N, V], ![D, N, H], ![D, V, N], ![N, N, V], ![N, V, N], ![V, A, B], ![V, A, V],
       ![V, N, N]}

/-- `T3f` is admissible. -/
def S3f : Subst Letter Letter.sep 3 :=
  ⟨T3f, by native_decide, by native_decide⟩

/-- An arity-`3` table of `47` words. -/
def T3g : Letter → Finset (Fin 3 → Letter)
  | B =>
      {![A, H, N], ![B, A, H], ![B, B, B], ![B, D, V], ![B, H, D], ![B, V, A], ![H, D, N],
       ![H, N, A], ![V, H, A], ![V, H, H], ![V, N, D]}
  | N =>
      {![A, H, B], ![B, H, H], ![D, H, A], ![H, D, D], ![H, N, A], ![N, A, A], ![N, A, H],
       ![N, H, A], ![N, N, N], ![V, H, V]}
  | A =>
      {![A, A, A], ![A, A, H], ![A, B, N], ![B, N, A], ![H, H, N], ![H, N, H], ![N, A, N]}
  | D =>
      {![A, N, D], ![D, A, A], ![D, A, H], ![D, B, N], ![N, D, N], ![N, N, D]}
  | O =>
      ∅
  | H =>
      {![B, N, H], ![H, A, B], ![H, A, V], ![H, N, N], ![N, H, N]}
  | V =>
      {![A, N, V], ![D, N, H], ![D, V, N], ![N, N, V], ![N, V, N], ![V, A, B], ![V, A, V],
       ![V, N, N]}

/-- `T3g` is admissible. -/
def S3g : Subst Letter Letter.sep 3 :=
  ⟨T3g, by native_decide, by native_decide⟩

/-- An arity-`3` table of `45` words. -/
def T3h : Letter → Finset (Fin 3 → Letter)
  | .B =>
      {![.B, .B, .B], ![.B, .H, .A], ![.N, .A, .V], ![.N, .D, .H], ![.N, .V, .D], ![.A, .B, .H], ![.A, .H, .N], ![.A, .H, .D], ![.D, .B, .V], ![.D, .V, .N], ![.D, .V, .D], ![.H, .N, .D], ![.H, .D, .N], ![.H, .D, .D], ![.V, .N, .A], ![.V, .A, .B], ![.V, .D, .A]}
  | .N =>
      {![.B, .V, .D], ![.N, .N, .N], ![.N, .V, .A], ![.A, .N, .H], ![.A, .D, .H], ![.A, .H, .N], ![.D, .N, .V], ![.D, .D, .H], ![.D, .H, .N], ![.H, .V, .D]}
  | .A =>
      {![.N, .B, .D], ![.N, .D, .N], ![.D, .B, .B], ![.D, .A, .V], ![.D, .H, .A]}
  | .D =>
      {![.N, .B, .A], ![.N, .A, .N], ![.A, .B, .B], ![.A, .A, .V], ![.A, .H, .A]}
  | .O =>
      ∅
  | .H =>
      {![.N, .N, .V], ![.N, .V, .N], ![.V, .N, .N], ![.V, .V, .V]}
  | .V =>
      {![.N, .N, .H], ![.N, .H, .N], ![.H, .N, .N], ![.H, .V, .V]}

/-- `T3h` is admissible. -/
def S3h : Subst Letter Letter.sep 3 := ⟨T3h, by native_decide, by native_decide⟩

end Substitutions
end ShannonBounds
