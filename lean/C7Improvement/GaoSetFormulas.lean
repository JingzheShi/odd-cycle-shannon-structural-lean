import C7Improvement.BlockDisjoint
import C7Improvement.RecursiveFrames

namespace ShannonBounds.C7Improvement

open RichPortSystem

variable {Left Right : Type*} [Fintype Left] [Fintype Right]
variable [DecidableEq Left] [DecidableEq Right]
variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]

variable (left : RichPortSystem GL) (right : RichPortSystem GR)
variable (neutralSide hSide vSide : Finset Left)
variable (neutralIndependent : GL.IsIndepSet ↑neutralSide)
variable (hIndependent : GL.IsIndepSet ↑hSide) (vIndependent : GL.IsIndepSet ↑vSide)
variable (neutralSeparated : ∀ point ∈ neutralSide,
  ¬ (footprint left false point ∧ footprint left true point))

theorem heterogeneousGao_Xstar :
    (heterogeneousGao left right neutralSide hSide vSide
      neutralIndependent hIndependent vIndependent neutralSeparated).Xstar =
    (auxiliaryNeutral left neutralSide ×ˢ right.Xstar) ∪
      (outside left hSide ×ˢ right.Xc true) ∪ (outside left vSide ×ˢ right.Xc false) := by
  rw [heterogeneousGao, heterogeneousLift_Xstar, flip_Xstar, flip_Xc, flip_Xc]
  rfl

theorem heterogeneousGao_Xc (direction : Bool) :
    (heterogeneousGao left right neutralSide hSide vSide
      neutralIndependent hIndependent vIndependent neutralSeparated).Xc direction =
    (auxiliaryFoot left neutralSide direction ×ˢ right.Xstar) ∪
      (inside left (if direction then vSide else hSide) ×ˢ right.Xc (!direction)) := by
  rw [heterogeneousGao, heterogeneousLift_Xc, flip_Xstar, flip_Xc]

def coreBlockLetters : List (Letter × Letter) :=
  [(.B,.B), (.H,.D), (.V,.A), (.D,.V), (.A,.H)]

def portsBlockLetters : List (Letter × Letter) := [(.O,.N), (.N,.O)]

theorem core_ports_separated : ∀ core ∈ coreBlockLetters, ∀ port ∈ portsBlockLetters,
    Letter.sep core.1 port.1 = true ∨ Letter.sep core.2 port.2 = true := by
  native_decide

theorem fold_union_member {Point : Type*} [DecidableEq Point]
    (sets : List (Finset Point)) (point : Point) :
    point ∈ sets.foldr (fun first second => first ∪ second) ∅ ↔
      ∃ points ∈ sets, point ∈ points := by
  induction sets with
  | nil => simp
  | cons points sets inductionHypothesis =>
    simp only [List.foldr_cons, Finset.mem_union, inductionHypothesis,
      List.mem_cons, exists_eq_or_imp]

theorem gao_core_blocks : (gao left right).fam .B =
    (coreBlockLetters.map fun letters => left.fam letters.1 ×ˢ right.fam letters.2).foldr
      (fun first second => first ∪ second) ∅ := by
  let remaining := (coreBlockLetters.map fun letters => left.fam letters.1 ×ˢ right.fam letters.2).foldr
    (fun first second => first ∪ second) ∅
  have mainEqual : (gao left right).I = remaining ∪ (gao left right).ports := by
    rw [gao_I_blocks, gao_ports]
    simp only [remaining, coreBlockLetters, ordinaryBlocks, blockUnion, List.map_cons,
      List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty, RichPortSystem.fam, transversal]
    simp only [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
  have disjoint : Disjoint remaining (gao left right).ports := by
    rw [Finset.disjoint_left]
    intro point memberCore memberPorts
    obtain ⟨block, memberBlock, memberPoint⟩ := (fold_union_member _ point).mp memberCore
    obtain ⟨core, memberCoreLabel, rfl⟩ := List.mem_map.mp memberBlock
    rw [gao_ports, Finset.mem_union] at memberPorts
    rcases memberPorts with memberFirst | memberSecond
    · exact (Finset.disjoint_left.mp (separated_products_disjoint left right core (.N,.O)
        (core_ports_separated core memberCoreLabel (.N,.O) (by simp [portsBlockLetters]))))
        memberPoint memberFirst
    · exact (Finset.disjoint_left.mp (separated_products_disjoint left right core (.O,.N)
        (core_ports_separated core memberCoreLabel (.O,.N) (by simp [portsBlockLetters]))))
        memberPoint memberSecond
  change (gao left right).I \ (gao left right).ports = remaining
  rw [mainEqual, Finset.union_sdiff_distrib, Finset.sdiff_self, Finset.union_empty,
    Finset.sdiff_eq_self_iff_disjoint.mpr disjoint]

theorem inside_own : inside left left.X = left.Xstar := by
  ext point
  simp only [inside, Finset.mem_filter]
  constructor
  · rintro ⟨member, nearby⟩
    exact (near_neutral_iff left member).mp nearby
  · intro member
    exact ⟨left.Xstar_subset_X member,
      (near_neutral_iff left (left.Xstar_subset_X member)).mpr member⟩

end ShannonBounds.C7Improvement
