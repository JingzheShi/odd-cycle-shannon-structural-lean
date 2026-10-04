import C7Improvement.C3Data
import C7Improvement.G15Oriented
import C7Improvement.BaseXBridge

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 X10List

theorem list_nodup_from_card {Point : Type*} [DecidableEq Point] (points : List Point)
    (equalCard : points.toFinset.card = points.length) : points.Nodup := by
  exact Multiset.coe_nodup.mp (Multiset.toFinset_card_eq_card_iff_nodup.mp equalCard)

theorem baseAtom_nodup (letter : Letter) : (baseAtom letter).Nodup := baseAtom_nodup_check letter

theorem list_product_eq {PointLeft PointRight : Type*} [DecidableEq PointLeft] [DecidableEq PointRight]
    (left : List PointLeft) (right : List PointRight) :
    (left.flatMap fun first => right.map fun second => (first, second)).toFinset =
      left.toFinset ×ˢ right.toFinset := by
  ext point
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_map, Finset.mem_product]
  constructor
  · rintro ⟨first, memberFirst, second, memberSecond, equal⟩
    cases equal
    exact ⟨memberFirst, memberSecond⟩
  · rintro ⟨memberFirst, memberSecond⟩
    exact ⟨point.1, memberFirst, point.2, memberSecond, rfl⟩

theorem gao_auxiliary {PointLeft PointRight : Type*} [DecidableEq PointLeft] [DecidableEq PointRight]
    {leftGraph : SimpleGraph PointLeft} {rightGraph : SimpleGraph PointRight}
    [DecidableRel leftGraph.Adj] [DecidableRel rightGraph.Adj]
    (left : RichPortSystem leftGraph) (right : RichPortSystem rightGraph) :
    (gao left right).X = left.X ×ˢ right.X := rfl

theorem X10List_eq : X10List.toFinset = G10.X := by
  rw [X10List, list_product_eq, G10, gao_auxiliary, baseX_list_eq]

theorem X10List_nodup : X10List.Nodup := by
  apply list_nodup_from_card
  rw [X10List_eq, X10List_length_check]
  exact G10_profile.2.2.1

end ShannonBounds.C7Improvement
