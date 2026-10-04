import C7Improvement.Profile
import ShannonBounds.BaseC7

namespace ShannonBounds.C7Improvement

open RichPortSystem

variable {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]

theorem liftRPS_Xc (left : RichPortSystem GL) (right : RichPortSystem GR) (direction : Bool) :
    (liftRPS left right).Xc direction =
      (left.Xstar ×ˢ right.Xc direction) ∪ (left.Xc direction ×ˢ right.Xstar) := by
  ext point
  rw [RichPortSystem.mem_Xc]
  change (point ∈ liftX left right ∧ footprint (liftRPS left right) direction point) ↔ _
  simp only [Finset.mem_union, Finset.mem_product]
  constructor
  · rintro ⟨member, foot⟩
    exact (exists_liftEp_conflict_iff left right member direction).mp foot
  · intro member
    have memberAux : point ∈ liftX left right := by
      rw [liftX, Finset.mem_product]
      rcases member with member | member
      · exact ⟨left.Xstar_subset_X member.1, right.Xc_subset_X direction member.2⟩
      · exact ⟨left.Xc_subset_X direction member.1, right.Xstar_subset_X member.2⟩
    exact ⟨memberAux, (exists_liftEp_conflict_iff left right memberAux direction).mpr member⟩

theorem card_liftRPS_Xc (left : RichPortSystem GL) (right : RichPortSystem GR) (direction : Bool) :
    ((liftRPS left right).Xc direction).card =
      left.Xstar.card * (right.Xc direction).card + (left.Xc direction).card * right.Xstar.card := by
  rw [liftRPS_Xc, Finset.card_union_of_disjoint
    (Finset.disjoint_product.mpr (Or.inl (neutral_disjoint_class left direction))),
    Finset.card_product, Finset.card_product]

theorem gao_N (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao left right).N = (left.N - left.d) * (right.N - right.d) + left.L * right.d + left.d * right.L :=
  card_liftSet left (flip right)

theorem gao_d (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao left right).d = left.eta * right.d + left.d * right.eta := by
  rw [gao, liftRPS_d]
  simp only [RichPortSystem.eta, flip_Xstar]
  rfl

theorem gao_L (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao left right).L = left.L * right.L := liftRPS_L left (flip right)

theorem gao_eta (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao left right).eta = left.eta * right.eta + (left.L - left.eta) * (right.L - right.eta) := by
  rw [gao, liftRPS_eta]
  simp only [RichPortSystem.eta, flip_Xstar]
  rfl

theorem gao_Xstar (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao left right).Xstar = (left.Xstar ×ˢ right.Xstar) ∪
      ((left.X \ left.Xstar) ×ˢ (right.X \ right.Xstar)) := by
  rw [gao, liftRPS_Xstar, liftNeutral, flip_Xstar]
  rfl

theorem gao_Xc (left : RichPortSystem GL) (right : RichPortSystem GR) (direction : Bool) :
    (gao left right).Xc direction =
      (left.Xstar ×ˢ right.Xc (!direction)) ∪ (left.Xc direction ×ˢ right.Xstar) := by
  rw [gao, liftRPS_Xc, flip_Xc, flip_Xstar]

theorem gao_neutral_flip_left (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao (flip left) right).Xstar = (gao left right).Xstar := by
  rw [gao_Xstar, gao_Xstar, flip_Xstar]
  rfl

theorem gao_neutral_flip_right (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao left (flip right)).Xstar = (gao left right).Xstar := by
  rw [gao_Xstar, gao_Xstar, flip_Xstar]
  rfl

def G10 : RichPortSystem (strongProd BaseC7.G5 BaseC7.G5) := gao BaseC7.base BaseC7.base

def G10A : RichPortSystem (strongProd BaseC7.G5 BaseC7.G5) := gao (flip BaseC7.base) BaseC7.base

def G10D : RichPortSystem (strongProd BaseC7.G5 BaseC7.G5) := gao BaseC7.base (flip BaseC7.base)

theorem G10_profile : G10.N = 134753 ∧ G10.d = 5152 ∧ G10.L = 134689 ∧ G10.eta = 105709 ∧
    (G10.Xc true).card = 14490 ∧ (G10.Xc false).card = 14490 := by
  have neutralCard : BaseC7.base.Xstar.card = 322 := BaseC7.base_eta
  simp only [G10, gao_N, gao_d, gao_L, gao_eta,
    BaseC7.base_N, BaseC7.base_d, BaseC7.base_L, BaseC7.base_eta]
  norm_num
  constructor <;> rw [gao, card_liftRPS_Xc, flip_Xc, flip_Xstar]
  all_goals simp only [Bool.not_true, Bool.not_false, BaseC7.base_Xc_false, BaseC7.base_Xc_true, neutralCard]

theorem G10A_neutral : G10A.Xstar = G10.Xstar := gao_neutral_flip_left BaseC7.base BaseC7.base

theorem G10D_neutral : G10D.Xstar = G10.Xstar := gao_neutral_flip_right BaseC7.base BaseC7.base

end ShannonBounds.C7Improvement
