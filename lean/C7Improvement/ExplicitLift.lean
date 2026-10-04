import C7Improvement.Ordinary

namespace ShannonBounds.C7Improvement

open RichPortSystem

variable {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]

def transversal (system : RichPortSystem GL) (direction : Bool) : Finset Left :=
  system.ports.image (system.ep direction)

@[simp] theorem flip_transversal (system : RichPortSystem GL) (direction : Bool) :
    transversal (flip system) direction = transversal system (!direction) := rfl

theorem auxiliary_partition (system : RichPortSystem GL) {point : Left}
    (member : point ∈ system.X) :
    point ∈ system.Xstar ∨ point ∈ system.Xc false ∨ point ∈ system.Xc true := by
  by_cases memberFalse : point ∈ system.Xc false
  · exact Or.inr (Or.inl memberFalse)
  by_cases memberTrue : point ∈ system.Xc true
  · exact Or.inr (Or.inr memberTrue)
  exact Or.inl (system.mem_Xstar.mpr ⟨member, memberFalse, memberTrue⟩)

theorem horizontal_blocks (left : RichPortSystem GL) (right : RichPortSystem GR) :
    right.ports.biUnion (hstrip left right) =
      (left.Xstar ×ˢ right.ports) ∪ (left.Xc false ×ˢ transversal right false) ∪
        (left.Xc true ×ˢ transversal right true) := by
  ext point
  simp only [Finset.mem_biUnion, mem_hstrip, Finset.mem_union, Finset.mem_product]
  constructor
  · rintro ⟨parent, memberParent, memberAux, endpoint⟩
    rcases auxiliary_partition left memberAux with neutral | memberFalse | memberTrue
    · rw [left.cls_eq_none_of_mem_Xstar neutral, RichPortSystem.epO_none] at endpoint
      exact Or.inl (Or.inl ⟨neutral, endpoint ▸ memberParent⟩)
    · rw [left.cls_eq_some_of_mem_Xc memberFalse, RichPortSystem.epO_some] at endpoint
      exact Or.inl (Or.inr ⟨memberFalse, Finset.mem_image.mpr ⟨parent, memberParent, endpoint.symm⟩⟩)
    · rw [left.cls_eq_some_of_mem_Xc memberTrue, RichPortSystem.epO_some] at endpoint
      exact Or.inr ⟨memberTrue, Finset.mem_image.mpr ⟨parent, memberParent, endpoint.symm⟩⟩
  · rintro ((⟨neutral, memberParent⟩ | ⟨memberFalse, endpointMember⟩) | ⟨memberTrue, endpointMember⟩)
    · refine ⟨point.2, memberParent, left.Xstar_subset_X neutral, ?_⟩
      rw [left.cls_eq_none_of_mem_Xstar neutral, RichPortSystem.epO_none]
    · obtain ⟨parent, memberParent, endpoint⟩ := Finset.mem_image.mp endpointMember
      refine ⟨parent, memberParent, left.Xc_subset_X false memberFalse, ?_⟩
      rw [left.cls_eq_some_of_mem_Xc memberFalse, RichPortSystem.epO_some]
      exact endpoint.symm
    · obtain ⟨parent, memberParent, endpoint⟩ := Finset.mem_image.mp endpointMember
      refine ⟨parent, memberParent, left.Xc_subset_X true memberTrue, ?_⟩
      rw [left.cls_eq_some_of_mem_Xc memberTrue, RichPortSystem.epO_some]
      exact endpoint.symm

theorem vertical_blocks (left : RichPortSystem GL) (right : RichPortSystem GR) :
    left.ports.biUnion (vstrip left right) =
      (left.ports ×ˢ right.Xstar) ∪ (transversal left true ×ˢ right.Xc false) ∪
        (transversal left false ×ˢ right.Xc true) := by
  ext point
  simp only [Finset.mem_biUnion, mem_vstrip, Finset.mem_union, Finset.mem_product]
  constructor
  · rintro ⟨parent, memberParent, memberAux, endpoint⟩
    rcases auxiliary_partition right memberAux with neutral | memberFalse | memberTrue
    · rw [right.cls_eq_none_of_mem_Xstar neutral] at endpoint
      change point.1 = parent at endpoint
      exact Or.inl (Or.inl ⟨endpoint ▸ memberParent, neutral⟩)
    · rw [right.cls_eq_some_of_mem_Xc memberFalse] at endpoint
      change point.1 = left.ep true parent at endpoint
      exact Or.inl (Or.inr ⟨Finset.mem_image.mpr ⟨parent, memberParent, endpoint.symm⟩, memberFalse⟩)
    · rw [right.cls_eq_some_of_mem_Xc memberTrue] at endpoint
      change point.1 = left.ep false parent at endpoint
      exact Or.inr ⟨Finset.mem_image.mpr ⟨parent, memberParent, endpoint.symm⟩, memberTrue⟩
  · rintro ((⟨memberParent, neutral⟩ | ⟨endpointMember, memberFalse⟩) | ⟨endpointMember, memberTrue⟩)
    · refine ⟨point.1, memberParent, right.Xstar_subset_X neutral, ?_⟩
      rw [right.cls_eq_none_of_mem_Xstar neutral]
      rfl
    · obtain ⟨parent, memberParent, endpoint⟩ := Finset.mem_image.mp endpointMember
      refine ⟨parent, memberParent, right.Xc_subset_X false memberFalse, ?_⟩
      rw [right.cls_eq_some_of_mem_Xc memberFalse]
      exact endpoint.symm
    · obtain ⟨parent, memberParent, endpoint⟩ := Finset.mem_image.mp endpointMember
      refine ⟨parent, memberParent, right.Xc_subset_X true memberTrue, ?_⟩
      rw [right.cls_eq_some_of_mem_Xc memberTrue]
      exact endpoint.symm

def ordinaryBlocks (left : RichPortSystem GL) (right : RichPortSystem GR) :
    List (Finset Left × Finset Right) :=
  [(left.I \ left.ports, right.I \ right.ports),
   (left.ports, right.Xstar),
   (transversal left true, right.Xc true),
   (transversal left false, right.Xc false),
   (left.Xstar, right.ports),
   (left.Xc true, transversal right false),
   (left.Xc false, transversal right true)]

def blockUnion (blocks : List (Finset Left × Finset Right)) : Finset (Left × Right) :=
  blocks.foldr (fun block accumulated => (block.1 ×ˢ block.2) ∪ accumulated) ∅

theorem gao_I_blocks (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao left right).I = blockUnion (ordinaryBlocks left right) := by
  rw [gao, liftRPS_I, liftSet, horizontal_blocks, vertical_blocks]
  simp only [flip_Xc, flip_Xstar, flip_transversal, Bool.not_true, Bool.not_false,
    blockUnion, ordinaryBlocks, List.foldr_cons, List.foldr_nil, Finset.union_empty, core]
  change _ = _
  simp only [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
  rfl

end ShannonBounds.C7Improvement
