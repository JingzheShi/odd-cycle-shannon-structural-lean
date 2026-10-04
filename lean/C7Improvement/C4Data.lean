import C7Improvement.Atoms10Data
import C7Improvement.PackedIndex

namespace ShannonBounds.C7Improvement

open BaseC7
open scoped BigOperators

def JqList := JplusList.filter fun point => !(inNeutral10 point)
def JnList := JplusList.filter inNeutral10

def tenAtomList (index : Fin 13) : List (BaseC7.Code × BaseC7.Code) :=
  match index.val with
  | 0 => atom10 .B
  | 1 => atom10 .N
  | 2 => atom10 .A
  | 3 => atom10 .D
  | 4 => atom10 .O
  | 5 => atom10 .H
  | 6 => atom10 .V
  | 7 => baseProductList .N .A ++ baseProductList .N .D ++
      baseProductList .A .N ++ baseProductList .D .N
  | 8 => X10List
  | 9 => JqList
  | 10 => JnList
  | 11 => baseProductList .N .A ++ baseProductList .A .N
  | _ => baseProductList .N .D ++ baseProductList .D .N

def fiveAtomList (index : Fin 8) : List BaseC7.Code :=
  match index.val with
  | 0 => baseAtom .B
  | 1 => baseAtom .N
  | 2 => baseAtom .A
  | 3 => baseAtom .D
  | 4 => baseAtom .O
  | 5 => baseAtom .H
  | 6 => baseAtom .V
  | _ => restList

def fifteenPieces : Letter → List (Fin 13 × Fin 8)
  | .B => [(0,0), (5,3), (6,2), (3,6), (2,5)]
  | .N => [(1,1), (9,3), (9,2)]
  | .A => [(2,1), (10,3)]
  | .D => [(3,1), (10,2)]
  | .O => [(4,1), (1,4)]
  | .H => [(5,1), (1,6)]
  | .V => [(6,1), (1,5)]

def crossPieces (left right : List (Fin 13 × Fin 8)) :=
  left.flatMap fun first => right.map fun second => (first, second)

def C4source := mainBlockLetters.flatMap fun letters =>
  crossPieces (fifteenPieces letters.1) (fifteenPieces letters.2)

def C4reference :=
  crossPieces [(1,1), (7,7)] [(1,1), (9,3), (7,2)] ++
    crossPieces [(7,1), (1,7)] [(11,1), (1,2), (12,1), (10,3)]

def jqIndex := buildPackedIndex fastNeighbors5 JqList
def jnIndex := buildPackedIndex fastNeighbors5 JnList

def aNearTable : Array Bool := Array.ofFn fun point : BaseC7.Code =>
  (baseAtom .A).any fun witness => wconf point witness
def dNearTable : Array Bool := Array.ofFn fun point : BaseC7.Code =>
  (baseAtom .D).any fun witness => wconf point witness

def aNear (point : BaseC7.Code) :=
  aNearTable[point.val]'(by simpa only [aNearTable, Array.size_ofFn] using point.isLt)
def dNear (point : BaseC7.Code) :=
  dNearTable[point.val]'(by simpa only [dNearTable, Array.size_ofFn] using point.isLt)

def right10Flags (point : BaseC7.Code × BaseC7.Code) : Fin 6 → Bool :=
  ![inNeutral10 point, inRest10 point, jqIndex.query point, jnIndex.query point,
    (neutralNear point.1 && aNear point.2) || (aNear point.1 && neutralNear point.2),
    (neutralNear point.1 && dNear point.2) || (dNear point.1 && neutralNear point.2)]

def right5Flags (point : BaseC7.Code) : Fin 3 → Bool :=
  ![neutralNear point, aNear point, dNear point]

def encodeFlags {bits : ℕ} (flags : Fin bits → Bool) : ℕ :=
  ∑ index : Fin bits, if flags index then 2 ^ index.val else 0

def decodeFlags {bits : ℕ} (mask : Fin (2 ^ bits)) : Fin bits → Bool :=
  fun index => mask.val.testBit index.val

def left10Samples : Array (List ℕ) := Array.ofFn fun atom : Fin 13 =>
  (tenAtomList atom).map fun point => encodeFlags (flags10 (transformPair point))
def left5Samples : Array (List ℕ) := Array.ofFn fun atom : Fin 8 =>
  (fiveAtomList atom).map fun point => encodeFlags (flags5 (transform point))
def right10Samples : Array (List ℕ) := Array.ofFn fun atom : Fin 13 =>
  (tenAtomList atom).map fun point => encodeFlags (right10Flags (transformPair point))
def right5Samples : Array (List ℕ) := Array.ofFn fun atom : Fin 8 =>
  (fiveAtomList atom).map fun point => encodeFlags (right5Flags (transform point))

def left10Weights : Array (Array ℕ) := Array.ofFn fun atom : Fin 13 =>
  Array.ofFn fun mask : Fin 4 =>
    (left10Samples[atom.val]'(by simp [left10Samples])).count mask.val
def left5Weights : Array (Array ℕ) := Array.ofFn fun atom : Fin 8 =>
  Array.ofFn fun mask : Fin 4 =>
    (left5Samples[atom.val]'(by simp [left5Samples])).count mask.val
def right10Weights : Array (Array ℕ) := Array.ofFn fun atom : Fin 13 =>
  Array.ofFn fun mask : Fin 64 =>
    (right10Samples[atom.val]'(by simp [right10Samples])).count mask.val
def right5Weights : Array (Array ℕ) := Array.ofFn fun atom : Fin 8 =>
  Array.ofFn fun mask : Fin 8 =>
    (right5Samples[atom.val]'(by simp [right5Samples])).count mask.val

def weightL10 (atom : Fin 13) (mask : Fin 4) :=
  left10Weights[atom.val][mask.val]'(by
    simpa only [left10Weights, Array.getElem_ofFn, Array.size_ofFn] using mask.isLt)
def weightL5 (atom : Fin 8) (mask : Fin 4) :=
  left5Weights[atom.val][mask.val]'(by
    simpa only [left5Weights, Array.getElem_ofFn, Array.size_ofFn] using mask.isLt)
def weightR10 (atom : Fin 13) (mask : Fin 64) :=
  right10Weights[atom.val][mask.val]'(by
    simpa only [right10Weights, Array.getElem_ofFn, Array.size_ofFn] using mask.isLt)
def weightR5 (atom : Fin 8) (mask : Fin 8) :=
  right5Weights[atom.val][mask.val]'(by
    simpa only [right5Weights, Array.getElem_ofFn, Array.size_ofFn] using mask.isLt)

def tenLeftSlot (atom : Fin 13) : Fin 2 := if atom.val = 1 then 0 else 1
def fiveLeftSlot (atom : Fin 8) : Fin 2 := if atom.val = 1 then 0 else 1
def tenRightSlot (atom : Fin 13) : Fin 6 :=
  match atom.val with | 1 => 0 | 7 => 1 | 9 => 2 | 10 => 3 | 11 => 4 | _ => 5
def fiveRightSlot (atom : Fin 8) : Fin 3 :=
  match atom.val with | 1 => 0 | 2 => 1 | _ => 2

def C4accept (left10 : Fin 4) (left5 : Fin 4) (right10 : Fin 64) (right5 : Fin 8) : Bool :=
  C4reference.all fun reference => !(
    decodeFlags left10 (tenLeftSlot reference.1.1) &&
    decodeFlags left5 (fiveLeftSlot reference.1.2) &&
    decodeFlags right10 (tenRightSlot reference.2.1) &&
    decodeFlags right5 (fiveRightSlot reference.2.2))

def C4blockCount (block : (Fin 13 × Fin 8) × (Fin 13 × Fin 8)) : ℕ :=
  ∑ left10 : Fin 4, ∑ left5 : Fin 4, ∑ right10 : Fin 64, ∑ right5 : Fin 8,
    if C4accept left10 left5 right10 right5 then
      weightL10 block.1.1 left10 * weightL5 block.1.2 left5 *
        weightR10 block.2.1 right10 * weightR5 block.2.2 right5 else 0

end ShannonBounds.C7Improvement
