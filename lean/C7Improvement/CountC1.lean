import C7Improvement.C1Data
import C7Improvement.Histogram

namespace ShannonBounds.C7Improvement

open BaseC7

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem listNear_spec (points : List BaseC7.Code) (point : BaseC7.Code) :
    (points.any fun witness => wconf point witness) = true ↔ near G5 points.toFinset point := by
  simp only [List.any_eq_true, near, List.mem_toFinset, conflict_G5]

theorem neutralNear_spec (point : BaseC7.Code) :
    neutralNear point = true ↔ near G5 BaseC7.base.Xstar point := by
  rw [neutralNear_lookup_check point, listNear_spec, baseAtom_eq]
  rfl

theorem restList_eq : restList.toFinset = BaseC7.base.X \ BaseC7.base.Xstar := by
  rw [restList, List.toFinset_append, baseAtom_eq, baseAtom_eq]
  change BaseC7.base.Xc false ∪ BaseC7.base.Xc true = BaseC7.base.X \ BaseC7.base.Xstar
  ext point
  rw [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro member
    rcases member with memberFalse | memberTrue
    · exact ⟨BaseC7.base.Xc_subset_X false memberFalse,
        fun neutral => (BaseC7.base.mem_Xstar.mp neutral).2.1 memberFalse⟩
    · exact ⟨BaseC7.base.Xc_subset_X true memberTrue,
        fun neutral => (BaseC7.base.mem_Xstar.mp neutral).2.2 memberTrue⟩
  · rintro ⟨memberX, notNeutral⟩
    by_cases memberFalse : point ∈ BaseC7.base.Xc false
    · exact Or.inl memberFalse
    by_cases memberTrue : point ∈ BaseC7.base.Xc true
    · exact Or.inr memberTrue
    exact False.elim (notNeutral (BaseC7.base.mem_Xstar.mpr ⟨memberX, memberFalse, memberTrue⟩))

theorem restNear_spec (point : BaseC7.Code) :
    restNear point = true ↔ near G5 (BaseC7.base.X \ BaseC7.base.Xstar) point := by
  rw [restNear_lookup_check point, listNear_spec, restList_eq]

theorem inNeutral10_spec (point : BaseC7.Code × BaseC7.Code) :
    inNeutral10 point = true ↔ near (strongProd G5 G5) G10.Xstar point := by
  rw [G10, gao_Xstar, near_union, near_product, near_product]
  simp only [inNeutral10, Bool.or_eq_true, Bool.and_eq_true, neutralNear_spec, restNear_spec]

theorem JplusList_eq : JplusList.toFinset = Jplus := by
  rw [JplusList, List.toFinset_append, Jplus]
  have filtered :
      (raw10List.filter fun point => !((exchangePairs.map Prod.fst).contains point)).toFinset =
      rawJ10 \ exchangeRemoved := by
    rw [← raw10List_eq, ← removed_eq]
    ext point
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_sdiff,
      bool_neg_true, List.contains_iff_mem]
  rw [filtered]
  rfl

theorem JplusList_nodup : JplusList.Nodup := by
  have equalCard : (JplusList : Multiset (BaseC7.Code × BaseC7.Code)).toFinset.card =
      (JplusList : Multiset (BaseC7.Code × BaseC7.Code)).card := by
    change JplusList.toFinset.card = JplusList.length
    rw [JplusList_eq, Jplus_card, JplusList_length]
  exact Multiset.coe_nodup.mp (Multiset.toFinset_card_eq_card_iff_nodup.mp equalCard)

theorem C1_count : (Jplus.filter fun point =>
    ¬ near (strongProd G5 G5) G10.Xstar point).card = 27488 := by
  have equalSets :
      Jplus.filter (fun point => ¬ near (strongProd G5 G5) G10.Xstar point) =
      (JplusList.filter fun point => !(inNeutral10 point)).toFinset := by
    ext point
    rw [Finset.mem_filter, ← JplusList_eq, List.mem_toFinset, List.mem_toFinset, List.mem_filter]
    simp only [bool_neg_true, inNeutral10_spec]
  rw [equalSets, List.toFinset_card_of_nodup (JplusList_nodup.filter _), C1_count_check]

end ShannonBounds.C7Improvement
