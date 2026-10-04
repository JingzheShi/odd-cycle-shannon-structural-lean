import C7Improvement.BaseLists

namespace ShannonBounds.C7Improvement

open RichPortSystem

theorem mainBlockLetters_separated : mainBlockLetters.Pairwise (fun first second =>
    Letter.sep first.1 second.1 = true ∨ Letter.sep first.2 second.2 = true) := by
  native_decide

theorem separated_products_disjoint {Left Right : Type*} [Fintype Left] [Fintype Right]
    [DecidableEq Left] [DecidableEq Right] {GL : SimpleGraph Left} {GR : SimpleGraph Right}
    [DecidableRel GL.Adj] [DecidableRel GR.Adj]
    (left : RichPortSystem GL) (right : RichPortSystem GR)
    (first second : Letter × Letter)
    (separated : Letter.sep first.1 second.1 = true ∨ Letter.sep first.2 second.2 = true) :
    Disjoint (left.fam first.1 ×ˢ right.fam first.2)
      (left.fam second.1 ×ˢ right.fam second.2) := by
  apply Finset.disjoint_left.mpr
  intro point memberFirst memberSecond
  obtain ⟨firstLeft, firstRight⟩ := Finset.mem_product.mp memberFirst
  obtain ⟨secondLeft, secondRight⟩ := Finset.mem_product.mp memberSecond
  rcases separated with separated | separated
  · exact left.sep_fam _ _ separated point.1 firstLeft point.1 secondLeft (conflict_rfl _)
  · exact right.sep_fam _ _ separated point.2 firstRight point.2 secondRight (conflict_rfl _)

theorem disjoint_fold_union {Point : Type*} [DecidableEq Point]
    (points : Finset Point) (sets : List (Finset Point))
    (disjoint : ∀ other ∈ sets, Disjoint points other) :
    Disjoint points (sets.foldr (fun first second => first ∪ second) ∅) := by
  induction sets with
  | nil => simp
  | cons next rest inductionHypothesis =>
    simp only [List.foldr_cons, Finset.disjoint_union_right]
    exact ⟨disjoint next (by simp),
      inductionHypothesis (fun other member => disjoint other (by simp [member]))⟩

theorem card_filter_unions {Point : Type*} [DecidableEq Point]
    (sets : List (Finset Point)) (disjoint : sets.Pairwise Disjoint)
    (accepted : Point → Prop) [DecidablePred accepted] :
    ((sets.foldr (fun first second => first ∪ second) ∅).filter accepted).card =
      (sets.map fun points => (points.filter accepted).card).sum := by
  induction sets with
  | nil => simp
  | cons points sets inductionHypothesis =>
    obtain ⟨headDisjoint, tailDisjoint⟩ := List.pairwise_cons.mp disjoint
    have unionDisjoint := disjoint_fold_union points sets headDisjoint
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, Finset.filter_union]
    rw [Finset.card_union_of_disjoint (unionDisjoint.mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)), inductionHypothesis tailDisjoint]

end ShannonBounds.C7Improvement
