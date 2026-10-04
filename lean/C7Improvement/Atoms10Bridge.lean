import C7Improvement.Atoms10Data
import C7Improvement.Atoms10
import C7Improvement.OrdinaryTransversal

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 10000
set_option maxHeartbeats 300000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 main10List

theorem ports10Bool_spec (point : BaseC7.Code × BaseC7.Code) :
    ports10Bool point = true ↔ point ∈ G10.ports := by
  rw [G10, gao_ports]
  simp only [ports10Bool, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem,
    ← List.mem_toFinset, baseAtom_eq, RichPortSystem.fam, Finset.mem_union, Finset.mem_product]
  exact or_comm

theorem ports10List_eq : ports10List.toFinset = G10.ports := by
  rw [ports10List, List.toFinset_append, baseProductList_eq, baseProductList_eq, G10, gao_ports]
  rfl

theorem atom10_eq (letter : Letter) : (atom10 letter).toFinset = G10.fam letter := by
  cases letter
  · change (main10List.filter fun point => !(ports10Bool point)).toFinset = G10.I \ G10.ports
    ext point
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_sdiff, bool_neg_true,
      ports10Bool_spec, ← main10List_eq, List.mem_toFinset]
  · change (baseProductList .N .N ++ productList restList restList).toFinset = G10.Xstar
    rw [List.toFinset_append, baseProductList_eq, productList, list_product_eq,
      restList_eq, G10, gao_Xstar]
    rfl
  · change (baseProductList .N .D ++ baseProductList .A .N).toFinset = G10.Xc false
    rw [List.toFinset_append, baseProductList_eq, baseProductList_eq, G10, gao_Xc]
    rfl
  · change (baseProductList .N .A ++ baseProductList .D .N).toFinset = G10.Xc true
    rw [List.toFinset_append, baseProductList_eq, baseProductList_eq, G10, gao_Xc]
    rfl
  · exact ports10List_eq
  · change (baseProductList .H .N ++ baseProductList .N .V).toFinset = transversal G10 true
    rw [List.toFinset_append, baseProductList_eq, baseProductList_eq, G10, gao_transversal]
    exact Finset.union_comm _ _
  · change (baseProductList .V .N ++ baseProductList .N .H).toFinset = transversal G10 false
    rw [List.toFinset_append, baseProductList_eq, baseProductList_eq, G10, gao_transversal]
    exact Finset.union_comm _ _

theorem atom10_card (letter : Letter) : (G10.fam letter).card = atom10Weight letter := by
  obtain ⟨mainSize, portsSize, auxiliarySize, neutralSize, horizontalSize, verticalSize⟩ := G10_profile
  cases letter
  · rw [card_fam_B, mainSize, portsSize]
    rfl
  · exact neutralSize
  · exact verticalSize
  · exact horizontalSize
  · exact portsSize
  · rw [card_fam_H]
    exact portsSize
  · rw [card_fam_V]
    exact portsSize

theorem atom10_nodup (letter : Letter) : (atom10 letter).Nodup := by
  apply list_nodup_from_card
  rw [atom10_eq, atom10_card, atom10_length_check]

end ShannonBounds.C7Improvement
