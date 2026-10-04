import ShannonBounds.TerminalCodes

namespace ShannonBounds.C7Improvement

open Letter

def C2 : Finset (Fin 2 → Letter) :=
  {![B, B], ![H, N], ![N, H], ![H, D], ![V, A], ![D, V], ![A, H]}

def K2 : Code Letter Letter.sep 2 := ⟨C2, by native_decide⟩

theorem K2_card : K2.C.card = 7 := by native_decide

end ShannonBounds.C7Improvement
