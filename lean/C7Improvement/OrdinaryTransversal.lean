import C7Improvement.ExplicitLift

namespace ShannonBounds.C7Improvement

open RichPortSystem

variable {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]

theorem lift_transversal (left : RichPortSystem GL) (right : RichPortSystem GR)
    (direction : Bool) : transversal (liftRPS left right) direction =
    (left.Xstar ×ˢ transversal right direction) ∪
      (transversal left direction ×ˢ right.Xstar) := by
  ext point
  constructor
  · intro member
    obtain ⟨parent, memberParent, endpoint⟩ := Finset.mem_image.mp member
    change liftEp left right direction parent = point at endpoint
    rcases (mem_liftPorts left right).mp memberParent with first | second
    · rw [liftEp_hport left right first.1] at endpoint
      cases endpoint
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr
        ⟨first.1, Finset.mem_image.mpr ⟨parent.2, first.2, rfl⟩⟩))
    · rw [liftEp_vport left right second.1] at endpoint
      cases endpoint
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨parent.1, second.1, rfl⟩, second.2⟩))
  · intro member
    rcases Finset.mem_union.mp member with first | second
    · obtain ⟨neutral, endpointMember⟩ := Finset.mem_product.mp first
      obtain ⟨parent, memberParent, endpoint⟩ := Finset.mem_image.mp endpointMember
      refine Finset.mem_image.mpr ⟨(point.1, parent),
        (mem_liftPorts left right).mpr (Or.inl ⟨neutral, memberParent⟩), ?_⟩
      change liftEp left right direction (point.1, parent) = point
      rw [liftEp_hport left right (p := (point.1, parent)) neutral]
      exact Prod.ext rfl endpoint
    · obtain ⟨endpointMember, neutral⟩ := Finset.mem_product.mp second
      obtain ⟨parent, memberParent, endpoint⟩ := Finset.mem_image.mp endpointMember
      refine Finset.mem_image.mpr ⟨(parent, point.2),
        (mem_liftPorts left right).mpr (Or.inr ⟨memberParent, neutral⟩), ?_⟩
      change liftEp left right direction (parent, point.2) = point
      rw [liftEp_vport left right (p := (parent, point.2)) memberParent]
      exact Prod.ext endpoint rfl

theorem gao_transversal (left : RichPortSystem GL) (right : RichPortSystem GR)
    (direction : Bool) : transversal (gao left right) direction =
    (left.Xstar ×ˢ transversal right (!direction)) ∪
      (transversal left direction ×ˢ right.Xstar) := by
  rw [gao, lift_transversal, flip_Xstar, flip_transversal]

theorem gao_ports (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao left right).ports = (left.Xstar ×ˢ right.ports) ∪ (left.ports ×ˢ right.Xstar) := by
  change liftPorts left (flip right) = _
  rw [liftPorts, flip_Xstar]
  rfl

end ShannonBounds.C7Improvement
