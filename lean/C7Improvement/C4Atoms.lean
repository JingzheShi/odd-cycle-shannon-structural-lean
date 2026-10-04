import C7Improvement.C4AtomData
import C7Improvement.GaoSetFormulas

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 10000
set_option maxHeartbeats 300000

attribute [local irreducible] BaseC7.base G10 G10A G15X Jplus

theorem JqList_eq : JqList.toFinset = outside G10 Jplus := by
  ext point
  simp only [JqList, List.mem_toFinset, List.mem_filter, bool_neg_true,
    inNeutral10_spec, outside, Finset.mem_filter, ← JplusList_eq, List.mem_toFinset]

theorem JnList_eq : JnList.toFinset = inside G10 Jplus := by
  ext point
  simp only [JnList, List.mem_toFinset, List.mem_filter, inNeutral10_spec,
    inside, Finset.mem_filter, ← JplusList_eq, List.mem_toFinset]

def tenAtomSet (index : Fin 13) : Finset (BaseC7.Code × BaseC7.Code) :=
  match index.val with
  | 0 => G10.fam .B | 1 => G10.fam .N | 2 => G10.fam .A | 3 => G10.fam .D
  | 4 => G10.fam .O | 5 => G10.fam .H | 6 => G10.fam .V
  | 7 => G10.X \ G10.Xstar | 8 => G10.X
  | 9 => outside G10 Jplus | 10 => inside G10 Jplus
  | 11 => G10A.Xc true | _ => G10A.Xc false

def fiveAtomSet (index : Fin 8) : Finset BaseC7.Code :=
  match index.val with
  | 0 => BaseC7.base.fam .B | 1 => BaseC7.base.fam .N | 2 => BaseC7.base.fam .A
  | 3 => BaseC7.base.fam .D | 4 => BaseC7.base.fam .O | 5 => BaseC7.base.fam .H
  | 6 => BaseC7.base.fam .V | _ => BaseC7.base.X \ BaseC7.base.Xstar

theorem tenAtomList_eq (index : Fin 13) : (tenAtomList index).toFinset = tenAtomSet index := by
  fin_cases index
  all_goals simp only [tenAtomList, tenAtomSet]
  · exact atom10_eq .B
  · exact atom10_eq .N
  · exact atom10_eq .A
  · exact atom10_eq .D
  · exact atom10_eq .O
  · exact atom10_eq .H
  · exact atom10_eq .V
  · rw [List.toFinset_append, List.toFinset_append, List.toFinset_append,
      baseProductList_eq, baseProductList_eq, baseProductList_eq, baseProductList_eq,
      G10_rest, rest_eq_classes BaseC7.base]
    simp only [RichPortSystem.fam, Finset.product_union, Finset.union_product,
      Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
  · exact X10List_eq
  · exact JqList_eq
  · exact JnList_eq
  · rw [List.toFinset_append, baseProductList_eq, baseProductList_eq, G10A, gao_Xc,
      flip_Xstar, flip_Xc]
    rfl
  · rw [List.toFinset_append, baseProductList_eq, baseProductList_eq, G10A, gao_Xc,
      flip_Xstar, flip_Xc]
    rfl

theorem fiveAtomList_eq (index : Fin 8) : (fiveAtomList index).toFinset = fiveAtomSet index := by
  fin_cases index
  all_goals simp only [fiveAtomList, fiveAtomSet]
  · exact baseAtom_eq .B
  · exact baseAtom_eq .N
  · exact baseAtom_eq .A
  · exact baseAtom_eq .D
  · exact baseAtom_eq .O
  · exact baseAtom_eq .H
  · exact baseAtom_eq .V
  · exact restList_eq

theorem tenAtomSet_card (index : Fin 13) : (tenAtomSet index).card = tenAtomSize index := by
  have outsideCard : (outside G10 Jplus).card = 27488 := C1_count
  fin_cases index
  all_goals simp only [tenAtomSet, tenAtomSize]
  · exact atom10_card .B
  · exact atom10_card .N
  · exact atom10_card .A
  · exact atom10_card .D
  · exact atom10_card .O
  · exact atom10_card .H
  · exact atom10_card .V
  · rw [Finset.card_sdiff_of_subset G10.Xstar_subset_X]
    have auxiliaryCard : G10.X.card = 134689 := G10_profile.2.2.1
    have neutralCard : G10.Xstar.card = 105709 := G10_profile.2.2.2.1
    rw [auxiliaryCard, neutralCard]
    rfl
  · exact G10_profile.2.2.1
  · exact C1_count
  · rw [inside_card, Jplus_card, outsideCard]
    rfl
  · exact G10A_profile.2.2.2.2.1
  · exact G10A_profile.2.2.2.2.2

theorem tenAtom_nodup (index : Fin 13) : (tenAtomList index).Nodup := by
  apply list_nodup_from_card
  rw [tenAtomList_eq, tenAtomSet_card, tenAtom_length_check]

theorem fiveAtom_nodup (index : Fin 8) : (fiveAtomList index).Nodup := by
  fin_cases index
  all_goals simp only [fiveAtomList]
  all_goals first | exact baseAtom_nodup _ | skip
  have disjoint : Disjoint (baseAtom .A).toFinset (baseAtom .D).toFinset := by
    rw [baseAtom_eq, baseAtom_eq]
    exact BaseC7.base.Xc_disjoint
  apply List.nodup_append.mpr
  exact ⟨baseAtom_nodup .A, baseAtom_nodup .D,
    fun first memberA second memberD equal => (Finset.disjoint_left.mp disjoint)
      (List.mem_toFinset.mpr memberA) (List.mem_toFinset.mpr (equal.symm ▸ memberD))⟩

theorem aNear_spec (point : BaseC7.Code) : aNear point = true ↔ near G5 (BaseC7.base.Xc false) point := by
  rw [aNear_lookup_check, listNear_spec, baseAtom_eq]
  rfl

theorem dNear_spec (point : BaseC7.Code) : dNear point = true ↔ near G5 (BaseC7.base.Xc true) point := by
  rw [dNear_lookup_check, listNear_spec, baseAtom_eq]
  rfl

end ShannonBounds.C7Improvement
