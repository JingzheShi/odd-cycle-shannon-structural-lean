import C7Improvement.Automorphism
import C7Improvement.Ordinary

namespace ShannonBounds.C7Improvement

open BaseC7

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def rawJ10 : Finset (BaseC7.Code × BaseC7.Code) := G10.I.image transformPair

theorem transformPair_injective : Function.Injective transformPair := by
  intro first second equal
  exact Prod.ext (transformEquiv.injective (congrArg Prod.fst equal))
    (transformEquiv.injective (congrArg Prod.snd equal))

theorem rawJ10_independent : (strongProd G5 G5).IsIndepSet ↑rawJ10 := by
  intro first memberFirst second memberSecond unequal adjacent
  obtain ⟨firstSource, memberSourceFirst, rfl⟩ := Finset.mem_image.mp memberFirst
  obtain ⟨secondSource, memberSourceSecond, rfl⟩ := Finset.mem_image.mp memberSecond
  have sourceUnequal : firstSource ≠ secondSource :=
    fun equal => unequal (congrArg transformPair equal)
  have sourceConflict := (transformPair_conflict firstSource secondSource).mp (Or.inr adjacent)
  exact not_conflict_of_indep G10.hI memberSourceFirst memberSourceSecond sourceUnequal sourceConflict

theorem rawJ10_card : rawJ10.card = 134753 := by
  rw [rawJ10, Finset.card_image_of_injective _ transformPair_injective]
  exact G10_profile.1

def exchangeRemoved : Finset (BaseC7.Code × BaseC7.Code) :=
  {(3660, 6494), (16388, 6494), (6494, 3660), (15643, 3660),
    (3660, 15643), (16388, 15643), (6494, 16388), (15643, 16388)}

def exchangeInsertedList : List (BaseC7.Code × BaseC7.Code) :=
  [(6110, 4092), (16046, 4092), (6494, 6110), (15643, 6110),
    (6110, 15685), (16046, 15685), (6494, 16046), (15643, 16046)]

def exchangeInserted : Finset (BaseC7.Code × BaseC7.Code) := exchangeInsertedList.toFinset

def Jplus : Finset (BaseC7.Code × BaseC7.Code) :=
  (rawJ10 \ exchangeRemoved) ∪ exchangeInserted

def pairConflict (first second : BaseC7.Code × BaseC7.Code) : Bool :=
  wconf first.1 second.1 && wconf first.2 second.2

theorem pairConflict_spec (first second : BaseC7.Code × BaseC7.Code) :
    pairConflict first second = true ↔ conflict (strongProd G5 G5) first second := by
  rw [conflict_strongProd_iff, conflict_G5, conflict_G5]
  simp only [pairConflict, Bool.and_eq_true]

theorem inserted_independent_check : exchangeInsertedList.all (fun first =>
    exchangeInsertedList.all (fun second => (first == second) || !(pairConflict first second))) = true := by
  native_decide

theorem inserted_independent : (strongProd G5 G5).IsIndepSet ↑exchangeInserted := by
  intro first memberFirst second memberSecond unequal adjacent
  have firstInList : first ∈ exchangeInsertedList := List.mem_toFinset.mp memberFirst
  have secondInList : second ∈ exchangeInsertedList := List.mem_toFinset.mp memberSecond
  have check := List.all_eq_true.mp
    (List.all_eq_true.mp inserted_independent_check first firstInList) second secondInList
  have confused := (pairConflict_spec first second).mpr (Or.inr adjacent)
  rw [confused] at check
  simpa [unequal] using check

end ShannonBounds.C7Improvement
