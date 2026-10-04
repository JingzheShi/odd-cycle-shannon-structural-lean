import ShannonBounds.PortRealisation
import Mathlib.Data.Fin.VecNotation

namespace ShannonBounds.ExplorationC13FrontierR03.TypeModel

abbrev Ty := Fin 58

def familyIndex : Letter → Nat
  | .B => 0
  | .N => 1
  | .A => 2
  | .D => 3
  | .O => 4
  | .H => 5
  | .V => 6

def family (a : Ty) : Letter :=
  match a.val with
  | 0 => Letter.B
  | 1 => Letter.B
  | 2 => Letter.B
  | 3 => Letter.B
  | 4 => Letter.B
  | 5 => Letter.B
  | 6 => Letter.B
  | 7 => Letter.B
  | 8 => Letter.N
  | 9 => Letter.N
  | 10 => Letter.A
  | 11 => Letter.A
  | 12 => Letter.A
  | 13 => Letter.A
  | 14 => Letter.A
  | 15 => Letter.A
  | 16 => Letter.A
  | 17 => Letter.A
  | 18 => Letter.D
  | 19 => Letter.D
  | 20 => Letter.D
  | 21 => Letter.D
  | 22 => Letter.D
  | 23 => Letter.D
  | 24 => Letter.D
  | 25 => Letter.D
  | 26 => Letter.O
  | 27 => Letter.O
  | 28 => Letter.O
  | 29 => Letter.O
  | 30 => Letter.O
  | 31 => Letter.O
  | 32 => Letter.O
  | 33 => Letter.O
  | 34 => Letter.O
  | 35 => Letter.O
  | 36 => Letter.O
  | 37 => Letter.O
  | 38 => Letter.O
  | 39 => Letter.O
  | 40 => Letter.O
  | 41 => Letter.O
  | 42 => Letter.H
  | 43 => Letter.H
  | 44 => Letter.H
  | 45 => Letter.H
  | 46 => Letter.H
  | 47 => Letter.H
  | 48 => Letter.H
  | 49 => Letter.H
  | 50 => Letter.V
  | 51 => Letter.V
  | 52 => Letter.V
  | 53 => Letter.V
  | 54 => Letter.V
  | 55 => Letter.V
  | 56 => Letter.V
  | 57 => Letter.V
  | _ => Letter.B

def mask (a : Ty) : Nat :=
  match a.val with
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 9
  | 5 => 11
  | 6 => 13
  | 7 => 15
  | 8 => 2
  | 9 => 3
  | 10 => 4
  | 11 => 5
  | 12 => 20
  | 13 => 21
  | 14 => 68
  | 15 => 69
  | 16 => 84
  | 17 => 85
  | 18 => 8
  | 19 => 9
  | 20 => 24
  | 21 => 25
  | 22 => 40
  | 23 => 41
  | 24 => 56
  | 25 => 57
  | 26 => 16
  | 27 => 20
  | 28 => 24
  | 29 => 28
  | 30 => 48
  | 31 => 52
  | 32 => 56
  | 33 => 60
  | 34 => 80
  | 35 => 84
  | 36 => 88
  | 37 => 92
  | 38 => 112
  | 39 => 116
  | 40 => 120
  | 41 => 124
  | 42 => 32
  | 43 => 40
  | 44 => 48
  | 45 => 56
  | 46 => 96
  | 47 => 104
  | 48 => 112
  | 49 => 120
  | 50 => 64
  | 51 => 68
  | 52 => 80
  | 53 => 84
  | 54 => 96
  | 55 => 100
  | 56 => 112
  | 57 => 116
  | _ => 1

def has (a : Ty) (b : Letter) : Bool := (mask a).testBit (familyIndex b)

def typedSep (a b : Ty) : Bool :=
  (decide (family a = family b) && decide (mask a ≠ mask b)) ||
    !(has a (family b)) || !(has b (family a))

theorem typedSep_symm : ∀ a b, typedSep a b = typedSep b a := by native_decide
theorem typedSep_irrefl : ∀ a, typedSep a a = false := by native_decide
theorem descriptors_injective : Function.Injective (fun a : Ty => (family a, mask a)) := by native_decide
theorem normalized : ∀ a : Ty, mask a < 128 ∧ has a (family a) = true ∧
    ∀ b : Letter, Letter.sep (family a) b = true → has a b = false := by native_decide

theorem normalized_complete : ∀ a : Letter, ∀ m : Fin 128,
    m.val.testBit (familyIndex a) = true →
    (∀ b : Letter, Letter.sep a b = true → m.val.testBit (familyIndex b) = false) →
    ∃ t : Ty, family t = a ∧ mask t = m.val := by native_decide


end ShannonBounds.ExplorationC13FrontierR03.TypeModel
