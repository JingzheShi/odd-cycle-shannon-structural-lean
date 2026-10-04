import C7Improvement.BaseLists
import C7Improvement.SideSets

namespace ShannonBounds.C7Improvement

open BaseC7

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def raw10List : List (BaseC7.Code × BaseC7.Code) := main10List.map transformPair

theorem raw10List_eq : raw10List.toFinset = rawJ10 := by
  rw [raw10List, rawJ10, ← main10List_eq]
  ext point
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

def exchangePairs : List ((BaseC7.Code × BaseC7.Code) × (BaseC7.Code × BaseC7.Code)) :=
  [((3660, 6494), (6110, 4092)), ((16388, 6494), (16046, 4092)),
   ((6494, 3660), (6494, 6110)), ((15643, 3660), (15643, 6110)),
   ((3660, 15643), (6110, 15685)), ((16388, 15643), (16046, 15685)),
   ((6494, 16388), (6494, 16046)), ((15643, 16388), (15643, 16046))]

theorem removed_eq : (exchangePairs.map Prod.fst).toFinset = exchangeRemoved := by native_decide

theorem inserted_eq : exchangePairs.map Prod.snd = exchangeInsertedList := by native_decide

theorem removed_members_check : exchangePairs.all (fun pair => raw10List.contains pair.1) = true := by
  native_decide

theorem inserted_absent_check : exchangeInsertedList.all (fun point => !(raw10List.contains point)) = true := by
  native_decide

theorem exchange_neighbor_check : exchangePairs.all (fun pair =>
    raw10List.all (fun point => !(pairConflict pair.2 point) || (point == pair.1))) = true := by
  native_decide

theorem removed_subset : exchangeRemoved ⊆ rawJ10 := by
  intro point member
  rw [← removed_eq, List.mem_toFinset, List.mem_map] at member
  obtain ⟨pair, memberPair, rfl⟩ := member
  rw [← raw10List_eq, List.mem_toFinset]
  exact List.contains_iff_mem.mp (List.all_eq_true.mp removed_members_check pair memberPair)

theorem inserted_absent {point : BaseC7.Code × BaseC7.Code} (member : point ∈ exchangeInserted) :
    point ∉ rawJ10 := by
  have memberList : point ∈ exchangeInsertedList := List.mem_toFinset.mp member
  have absent := List.all_eq_true.mp inserted_absent_check point memberList
  intro memberRaw
  have rawMember : point ∈ raw10List := by
    rw [← raw10List_eq, List.mem_toFinset] at memberRaw
    exact memberRaw
  have contained := List.contains_iff_mem.mpr rawMember
  rw [contained] at absent
  cases absent

theorem inserted_conflict_removed {inserted original : BaseC7.Code × BaseC7.Code}
    (memberInserted : inserted ∈ exchangeInserted) (memberOriginal : original ∈ rawJ10)
    (confused : conflict (strongProd G5 G5) inserted original) : original ∈ exchangeRemoved := by
  have insertedList : inserted ∈ exchangeInsertedList := List.mem_toFinset.mp memberInserted
  rw [← inserted_eq, List.mem_map] at insertedList
  obtain ⟨pair, memberPair, sameInserted⟩ := insertedList
  have originalList : original ∈ raw10List := by
    rw [← raw10List_eq, List.mem_toFinset] at memberOriginal
    exact memberOriginal
  have check := List.all_eq_true.mp
    (List.all_eq_true.mp exchange_neighbor_check pair memberPair) original originalList
  have flag : pairConflict pair.2 original = true := by
    rw [sameInserted]
    exact (pairConflict_spec inserted original).mpr confused
  rw [flag] at check
  have sameOriginal : original = pair.1 := by simpa using check
  rw [sameOriginal, ← removed_eq, List.mem_toFinset]
  exact List.mem_map.mpr ⟨pair, memberPair, rfl⟩

theorem Jplus_independent : (strongProd G5 G5).IsIndepSet ↑Jplus := by
  intro first memberFirst second memberSecond unequal adjacent
  rcases Finset.mem_union.mp memberFirst with memberFirst | memberFirst <;>
    rcases Finset.mem_union.mp memberSecond with memberSecond | memberSecond
  · exact rawJ10_independent (Finset.mem_sdiff.mp memberFirst).1
      (Finset.mem_sdiff.mp memberSecond).1 unequal adjacent
  · exact (Finset.mem_sdiff.mp memberFirst).2
      (inserted_conflict_removed memberSecond (Finset.mem_sdiff.mp memberFirst).1
        (conflict_symm (Or.inr adjacent)))
  · exact (Finset.mem_sdiff.mp memberSecond).2
      (inserted_conflict_removed memberFirst (Finset.mem_sdiff.mp memberSecond).1 (Or.inr adjacent))
  · exact inserted_independent memberFirst memberSecond unequal adjacent

theorem Jplus_card : Jplus.card = 134753 := by
  have disjointSets : Disjoint (rawJ10 \ exchangeRemoved) exchangeInserted := by
    rw [Finset.disjoint_left]
    intro point memberRaw memberNew
    exact inserted_absent memberNew (Finset.mem_sdiff.mp memberRaw).1
  have removedCard : exchangeRemoved.card = 8 := by native_decide
  have insertedCard : exchangeInserted.card = 8 := by native_decide
  rw [Jplus, Finset.card_union_of_disjoint disjointSets,
    Finset.card_sdiff_of_subset removed_subset, rawJ10_card, removedCard, insertedCard]

end ShannonBounds.C7Improvement
