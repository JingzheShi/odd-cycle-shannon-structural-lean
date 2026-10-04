import C7Improvement.C3Data

namespace ShannonBounds.C7Improvement

open BaseC7

def productList {Left Right : Type*} (left : List Left) (right : List Right) : List (Left × Right) :=
  left.flatMap fun first => right.map fun second => (first, second)

def ports10Bool (point : BaseC7.Code × BaseC7.Code) : Bool :=
  ((baseAtom .O).contains point.1 && (baseAtom .N).contains point.2) ||
    ((baseAtom .N).contains point.1 && (baseAtom .O).contains point.2)

def ports10List : List (BaseC7.Code × BaseC7.Code) :=
  baseProductList .N .O ++ baseProductList .O .N

def atom10 : Letter → List (BaseC7.Code × BaseC7.Code)
  | .B => main10List.filter fun point => !(ports10Bool point)
  | .N => baseProductList .N .N ++ productList restList restList
  | .A => baseProductList .N .D ++ baseProductList .A .N
  | .D => baseProductList .N .A ++ baseProductList .D .N
  | .O => ports10List
  | .H => baseProductList .H .N ++ baseProductList .N .V
  | .V => baseProductList .V .N ++ baseProductList .N .H

def atom10Weight : Letter → ℕ
  | .B => 129601
  | .N => 105709
  | .A => 14490
  | .D => 14490
  | .O | .H | .V => 5152

theorem atom10_length_check : ∀ letter : Letter, (atom10 letter).length = atom10Weight letter := by
  native_decide

end ShannonBounds.C7Improvement
