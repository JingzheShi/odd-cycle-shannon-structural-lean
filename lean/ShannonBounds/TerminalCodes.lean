/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.PortRealisation

/-!
# Terminal codes over the seven-letter separation system

Pairwise separated codes over the seven-letter separation system of `PortRealisation.lean`.
Each word list is given together with the proof that it is pairwise separated.
-/

namespace ShannonBounds
namespace TerminalCodes

open SimpleGraph Letter

set_option maxRecDepth 1000000
set_option exponentiation.threshold 20000
set_option synthInstance.maxSize 4000
set_option synthInstance.maxHeartbeats 4000000

/-! ### Arity 3 -/

/-- `19` words of length `3`. -/
def C3a : Finset (Fin 3 → Letter) :=
  {![A, B, V], ![A, H, N], ![A, V, H], ![B, A, B], ![B, D, D], ![B, H, A], ![B, N, B],
   ![D, A, H], ![D, D, N], ![D, N, H], ![H, B, A], ![H, H, H], ![H, V, N], ![N, B, V],
   ![N, H, N], ![N, V, H], ![V, B, D], ![V, B, N], ![V, V, A]}

/-- `C3a` is pairwise separated. -/
def K3a : Code Letter Letter.sep 3 := ⟨C3a, by native_decide⟩

/-! ### Arity 4 -/

/-- `49` words of length `4`. -/
def C4a : Finset (Fin 4 → Letter) :=
  {![B, B, B, B], ![B, N, V, B], ![B, A, H, B], ![B, D, V, B], ![B, H, N, B], ![B, H, D, B],
   ![B, V, A, B], ![N, B, B, V], ![N, N, V, H], ![N, A, V, H], ![N, D, H, H], ![N, H, N, H],
   ![N, H, A, H], ![N, V, D, V], ![A, B, B, V], ![A, N, H, H], ![A, A, V, H], ![A, D, H, H],
   ![A, H, A, H], ![A, V, N, H], ![A, V, D, H], ![D, B, B, H], ![D, N, V, V], ![D, A, V, V],
   ![D, D, H, V], ![D, H, N, V], ![D, H, A, V], ![D, V, D, V], ![H, B, B, A], ![H, N, V, D],
   ![H, A, H, D], ![H, A, V, N], ![H, D, H, N], ![H, D, V, D], ![H, H, N, N], ![H, H, N, D],
   ![H, H, A, N], ![H, H, D, D], ![H, V, A, D], ![H, V, D, N], ![V, B, B, N], ![V, B, B, D],
   ![V, N, V, N], ![V, N, V, A], ![V, A, H, A], ![V, D, V, A], ![V, H, D, A], ![V, V, N, A],
   ![V, V, A, A]}

/-- `C4a` is pairwise separated. -/
def K4a : Code Letter Letter.sep 4 := ⟨C4a, by native_decide⟩

/-- `57` words of length `4`. -/
def C4b : Finset (Fin 4 → Letter) :=
  {![A, A, A, V], ![A, A, N, V], ![A, B, H, A], ![A, H, A, A], ![A, H, A, N], ![A, H, N, A],
   ![A, H, N, N], ![A, N, A, V], ![A, N, D, H], ![A, N, H, N], ![A, N, N, H], ![A, V, D, B],
   ![B, A, D, H], ![B, A, V, N], ![B, B, B, B], ![B, B, V, D], ![B, D, B, H], ![B, D, H, N],
   ![B, H, H, H], ![B, V, A, D], ![B, V, N, D], ![D, A, V, A], ![D, H, H, A], ![D, N, B, V],
   ![D, N, V, A], ![D, N, V, N], ![D, V, B, A], ![D, V, B, N], ![H, A, B, H], ![H, B, D, B],
   ![H, B, V, H], ![H, D, A, B], ![H, D, N, B], ![H, N, N, D], ![H, V, H, D], ![H, V, H, N],
   ![N, A, A, V], ![N, A, N, V], ![N, B, H, A], ![N, H, A, N], ![N, H, B, A], ![N, N, A, V],
   ![N, N, D, H], ![N, N, N, V], ![N, N, V, N], ![N, V, D, N], ![N, V, H, A], ![N, V, N, N],
   ![V, A, A, B], ![V, A, N, B], ![V, D, D, H], ![V, H, A, H], ![V, H, N, H], ![V, N, A, B],
   ![V, N, N, A], ![V, N, N, N], ![V, V, H, V]}

/-- `C4b` is pairwise separated. -/
def K4b : Code Letter Letter.sep 4 := ⟨C4b, by native_decide⟩

end TerminalCodes
end ShannonBounds
