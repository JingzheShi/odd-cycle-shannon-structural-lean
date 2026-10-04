import C7Improvement.Exchanges

namespace ShannonBounds.C7Improvement

open BaseC7

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def neutralNearTable : Array Bool :=
  Array.ofFn fun point : BaseC7.Code => (baseAtom .N).any fun witness => wconf point witness

def restList : List BaseC7.Code := baseAtom .A ++ baseAtom .D

def restNearTable : Array Bool :=
  Array.ofFn fun point : BaseC7.Code => restList.any fun witness => wconf point witness

def neutralNear (point : BaseC7.Code) : Bool :=
  neutralNearTable[point.val]'(by simpa only [neutralNearTable, Array.size_ofFn] using point.isLt)

def restNear (point : BaseC7.Code) : Bool :=
  restNearTable[point.val]'(by simpa only [restNearTable, Array.size_ofFn] using point.isLt)

theorem neutralNear_lookup_check : ∀ point : BaseC7.Code,
    neutralNear point = ((baseAtom .N).any fun witness => wconf point witness) := by
  native_decide

theorem restNear_lookup_check : ∀ point : BaseC7.Code,
    restNear point = (restList.any fun witness => wconf point witness) := by native_decide

def inNeutral10 (point : BaseC7.Code × BaseC7.Code) : Bool :=
  (neutralNear point.1 && neutralNear point.2) || (restNear point.1 && restNear point.2)

def JplusList : List (BaseC7.Code × BaseC7.Code) :=
  (raw10List.filter fun point => !((exchangePairs.map Prod.fst).contains point)) ++ exchangeInsertedList

theorem JplusList_length : JplusList.length = 134753 := by native_decide

theorem C1_count_check : (JplusList.filter fun point => !(inNeutral10 point)).length = 27488 := by
  native_decide

end ShannonBounds.C7Improvement
