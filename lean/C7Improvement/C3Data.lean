import C7Improvement.C1Data
import ShannonBounds.CapCertC7

namespace ShannonBounds.C7Improvement

open BaseC7
open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def X10List : List (BaseC7.Code × BaseC7.Code) :=
  Xlist.flatMap fun first => Xlist.map fun second => (first, second)

def inRest10 (point : BaseC7.Code × BaseC7.Code) : Bool :=
  (neutralNear point.1 && restNear point.2) || (restNear point.1 && neutralNear point.2)

def flags10 (point : BaseC7.Code × BaseC7.Code) : Fin 2 → Bool :=
  ![inNeutral10 point, inRest10 point]

def flags5 (point : BaseC7.Code) : Fin 2 → Bool := ![neutralNear point, restNear point]

def weight10 (points : List (BaseC7.Code × BaseC7.Code)) (flags : Fin 2 → Bool) : ℕ :=
  (points.filter fun point => flags10 point == flags).length

def weight5 (points : List BaseC7.Code) (flags : Fin 2 → Bool) : ℕ :=
  (points.filter fun point => flags5 point == flags).length

def blockOutsideCount (left : List (BaseC7.Code × BaseC7.Code)) (right : List BaseC7.Code) : ℕ :=
  ∑ leftFlags : Fin 2 → Bool, ∑ rightFlags : Fin 2 → Bool,
    if ∀ index, !(leftFlags index && rightFlags index) = true then
      weight10 left leftFlags * weight5 right rightFlags else 0

def C3value : ℕ := blockOutsideCount X10List (baseAtom .N) +
  blockOutsideCount JplusList (baseAtom .D) + blockOutsideCount JplusList (baseAtom .A)

theorem baseAtom_length_check : ∀ letter : Letter, (baseAtom letter).length = CertC7.w0 letter := by
  native_decide

theorem baseAtom_nodup_check : ∀ letter : Letter, (baseAtom letter).Nodup := by native_decide

theorem X10List_length_check : X10List.length = 134689 := by native_decide

theorem C3_count_check : C3value = 14045805 := by native_decide

end ShannonBounds.C7Improvement
