import ShannonBounds.PortRealisation

namespace ShannonBounds.C7Improvement

open RichPortSystem

set_option maxHeartbeats 2000000

variable {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
variable {GL : SimpleGraph Left} {GR : SimpleGraph Right}
variable [DecidableRel GL.Adj] [DecidableRel GR.Adj]

def flip (system : RichPortSystem GL) : RichPortSystem GL where
  I := system.I
  hI := system.hI
  ports := system.ports
  hports := system.hports
  ep := fun direction parent => system.ep (!direction) parent
  side := fun parent => !system.side parent
  hep_parent := by simpa using system.hep_parent
  halt_not := by simpa using system.halt_not
  hprivate := by simpa using system.hprivate
  hep_conflict := by simpa using system.hep_conflict
  halt_inj := by simpa using system.halt_inj
  hP_indep := fun direction => system.hP_indep (!direction)
  X := system.X
  hX := system.hX
  hsep := by
    intro point member both
    exact system.hsep point member ⟨both.2, both.1⟩

@[simp] theorem flip_Xc (system : RichPortSystem GL) (direction : Bool) :
    (flip system).Xc direction = system.Xc (!direction) := rfl

@[simp] theorem flip_Xstar (system : RichPortSystem GL) :
    (flip system).Xstar = system.Xstar := by
  simp only [RichPortSystem.Xstar, flip_Xc]
  change system.X \ (system.Xc true ∪ system.Xc false) =
    system.X \ (system.Xc false ∪ system.Xc true)
  rw [Finset.union_comm]

def withAux (system : RichPortSystem GL) (auxiliary : Finset Left)
    (independent : GL.IsIndepSet ↑auxiliary)
    (separated : ∀ point ∈ auxiliary,
      ¬ ((∃ parent ∈ system.ports, conflict GL point (system.ep false parent)) ∧
         (∃ parent ∈ system.ports, conflict GL point (system.ep true parent)))) :
    RichPortSystem GL :=
  { system with X := auxiliary, hX := independent, hsep := separated }

def near (graph : SimpleGraph Left) [DecidableRel graph.Adj]
    (points : Finset Left) (point : Left) : Prop :=
  ∃ witness ∈ points, conflict graph point witness

instance (graph : SimpleGraph Left) [DecidableRel graph.Adj]
    (points : Finset Left) (point : Left) : Decidable (near graph points point) :=
  inferInstanceAs (Decidable (∃ witness ∈ points, conflict graph point witness))

def footprint (system : RichPortSystem GL) (direction : Bool) (point : Left) : Prop :=
  ∃ parent ∈ system.ports, conflict GL point (system.ep direction parent)

instance (system : RichPortSystem GL) (direction : Bool) (point : Left) :
    Decidable (footprint system direction point) :=
  inferInstanceAs (Decidable (∃ parent ∈ system.ports, conflict GL point (system.ep direction parent)))

theorem lift_footprint_iff (left : RichPortSystem GL) (right : RichPortSystem GR)
    (point : Left × Right) (direction : Bool) :
    footprint (liftRPS left right) direction point ↔
      (near GL left.Xstar point.1 ∧ footprint right direction point.2) ∨
      (footprint left direction point.1 ∧ near GR right.Xstar point.2) := by
  constructor
  · rintro ⟨parent, member, confused⟩
    change parent ∈ liftPorts left right at member
    change conflict (strongProd GL GR) point (liftEp left right direction parent) at confused
    rcases (mem_liftPorts left right).mp member with horizontal | vertical
    · rw [liftEp_hport left right horizontal.1] at confused
      exact Or.inl ⟨⟨parent.1, horizontal.1, (conflict_strongProd_iff.mp confused).1⟩,
        ⟨parent.2, horizontal.2, (conflict_strongProd_iff.mp confused).2⟩⟩
    · rw [liftEp_vport left right vertical.1] at confused
      exact Or.inr ⟨⟨parent.1, vertical.1, (conflict_strongProd_iff.mp confused).1⟩,
        ⟨parent.2, vertical.2, (conflict_strongProd_iff.mp confused).2⟩⟩
  · rintro (⟨⟨neutral, memberNeutral, conflictNeutral⟩, ⟨parent, memberParent, conflictParent⟩⟩ |
      ⟨⟨parent, memberParent, conflictParent⟩, ⟨neutral, memberNeutral, conflictNeutral⟩⟩)
    · refine ⟨(neutral, parent), ?_, ?_⟩
      · exact (mem_liftPorts left right).mpr (Or.inl ⟨memberNeutral, memberParent⟩)
      · change conflict (strongProd GL GR) point (liftEp left right direction (neutral, parent))
        rw [liftEp_hport left right memberNeutral]
        exact conflict_strongProd_iff.mpr ⟨conflictNeutral, conflictParent⟩
    · refine ⟨(parent, neutral), ?_, ?_⟩
      · exact (mem_liftPorts left right).mpr (Or.inr ⟨memberParent, memberNeutral⟩)
      · change conflict (strongProd GL GR) point (liftEp left right direction (parent, neutral))
        rw [liftEp_vport left right memberParent]
        exact conflict_strongProd_iff.mpr ⟨conflictParent, conflictNeutral⟩

theorem near_neutral_iff (system : RichPortSystem GL) {point : Left}
    (member : point ∈ system.X) :
    near GL system.Xstar point ↔ point ∈ system.Xstar := by
  constructor
  · rintro ⟨witness, memberWitness, confused⟩
    have equal := eq_of_conflict_of_indep system.hX member
      (system.Xstar_subset_X memberWitness) confused
    simpa [equal] using memberWitness
  · intro memberNeutral
    exact ⟨point, memberNeutral, conflict_rfl point⟩

def heterogeneousAux (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left) : Finset (Left × Right) :=
  (neutralSide ×ˢ right.Xstar) ∪ (falseSide ×ˢ right.Xc false) ∪
    (trueSide ×ˢ right.Xc true)

theorem mem_heterogeneousAux (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left) (point : Left × Right) :
    point ∈ heterogeneousAux right neutralSide falseSide trueSide ↔
      (point.1 ∈ neutralSide ∧ point.2 ∈ right.Xstar) ∨
      (point.1 ∈ falseSide ∧ point.2 ∈ right.Xc false) ∨
      (point.1 ∈ trueSide ∧ point.2 ∈ right.Xc true) := by
  simp only [heterogeneousAux, Finset.mem_union, Finset.mem_product]
  tauto

theorem heterogeneousAux_independent (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left)
    (neutralIndependent : GL.IsIndepSet ↑neutralSide)
    (falseIndependent : GL.IsIndepSet ↑falseSide)
    (trueIndependent : GL.IsIndepSet ↑trueSide) :
    (strongProd GL GR).IsIndepSet ↑(heterogeneousAux right neutralSide falseSide trueSide) := by
  intro first memberFirst second memberSecond unequal adjacent
  have confused : conflict (strongProd GL GR) first second := Or.inr adjacent
  have firstCases := (mem_heterogeneousAux right neutralSide falseSide trueSide first).mp memberFirst
  have secondCases := (mem_heterogeneousAux right neutralSide falseSide trueSide second).mp memberSecond
  have firstRight : first.2 ∈ right.X := by
    rcases firstCases with member | member | member
    · exact right.Xstar_subset_X member.2
    · exact right.Xc_subset_X false member.2
    · exact right.Xc_subset_X true member.2
  have secondRight : second.2 ∈ right.X := by
    rcases secondCases with member | member | member
    · exact right.Xstar_subset_X member.2
    · exact right.Xc_subset_X false member.2
    · exact right.Xc_subset_X true member.2
  have equalRight : first.2 = second.2 :=
    eq_of_conflict_of_indep right.hX firstRight secondRight (conflict_snd confused)
  have equalLeft : first.1 = second.1 := by
    rcases firstCases with firstNeutral | firstFalse | firstTrue <;>
      rcases secondCases with secondNeutral | secondFalse | secondTrue
    · exact eq_of_conflict_of_indep neutralIndependent firstNeutral.1 secondNeutral.1 (conflict_fst confused)
    · exact False.elim ((right.mem_Xstar.mp firstNeutral.2).2.1 (equalRight.symm ▸ secondFalse.2))
    · exact False.elim ((right.mem_Xstar.mp firstNeutral.2).2.2 (equalRight.symm ▸ secondTrue.2))
    · exact False.elim ((right.mem_Xstar.mp secondNeutral.2).2.1 (equalRight ▸ firstFalse.2))
    · exact eq_of_conflict_of_indep falseIndependent firstFalse.1 secondFalse.1 (conflict_fst confused)
    · exact False.elim (Finset.disjoint_left.mp right.Xc_disjoint (equalRight ▸ firstFalse.2) secondTrue.2)
    · exact False.elim ((right.mem_Xstar.mp secondNeutral.2).2.2 (equalRight ▸ firstTrue.2))
    · exact False.elim (Finset.disjoint_left.mp right.Xc_disjoint secondFalse.2 (equalRight ▸ firstTrue.2))
    · exact eq_of_conflict_of_indep trueIndependent firstTrue.1 secondTrue.1 (conflict_fst confused)
  exact unequal (Prod.ext equalLeft equalRight)

theorem heterogeneousAux_separated (left : RichPortSystem GL) (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left)
    (neutralSeparated : ∀ point ∈ neutralSide,
      ¬ (footprint left false point ∧ footprint left true point)) :
    ∀ point ∈ heterogeneousAux right neutralSide falseSide trueSide,
      ¬ (footprint (liftRPS left right) false point ∧
         footprint (liftRPS left right) true point) := by
  intro point member both
  have falseCases := (lift_footprint_iff left right point false).mp both.1
  have trueCases := (lift_footprint_iff left right point true).mp both.2
  rcases (mem_heterogeneousAux right neutralSide falseSide trueSide point).mp member with
    memberNeutral | memberFalse | memberTrue
  · have noFalse : ¬ footprint right false point.2 :=
      fun witness => by
        obtain ⟨parent, memberParent, confused⟩ := witness
        exact right.not_conflict_ep_of_mem_Xstar memberNeutral.2 false memberParent confused
    have noTrue : ¬ footprint right true point.2 :=
      fun witness => by
        obtain ⟨parent, memberParent, confused⟩ := witness
        exact right.not_conflict_ep_of_mem_Xstar memberNeutral.2 true memberParent confused
    exact neutralSeparated point.1 memberNeutral.1
      ⟨(falseCases.resolve_left (fun impossible => noFalse impossible.2)).1,
       (trueCases.resolve_left (fun impossible => noTrue impossible.2)).1⟩
  · have memberX := right.Xc_subset_X false memberFalse.2
    rcases trueCases with impossible | impossible
    · exact (right.notMem_Xc_of_mem_Xc memberFalse.2)
        (right.mem_Xc.mpr ⟨memberX, impossible.2⟩)
    · have memberNeutral := (near_neutral_iff right memberX).mp impossible.2
      exact (right.mem_Xstar.mp memberNeutral).2.1 memberFalse.2
  · have memberX := right.Xc_subset_X true memberTrue.2
    rcases falseCases with impossible | impossible
    · exact (right.notMem_Xc_of_mem_Xc memberTrue.2)
        (right.mem_Xc.mpr ⟨memberX, impossible.2⟩)
    · have memberNeutral := (near_neutral_iff right memberX).mp impossible.2
      exact (right.mem_Xstar.mp memberNeutral).2.2 memberTrue.2

def heterogeneousLift (left : RichPortSystem GL) (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left)
    (neutralIndependent : GL.IsIndepSet ↑neutralSide)
    (falseIndependent : GL.IsIndepSet ↑falseSide)
    (trueIndependent : GL.IsIndepSet ↑trueSide)
    (neutralSeparated : ∀ point ∈ neutralSide,
      ¬ (footprint left false point ∧ footprint left true point)) :
    RichPortSystem (strongProd GL GR) :=
  withAux (liftRPS left right) (heterogeneousAux right neutralSide falseSide trueSide)
    (heterogeneousAux_independent right neutralSide falseSide trueSide
      neutralIndependent falseIndependent trueIndependent)
    (heterogeneousAux_separated left right neutralSide falseSide trueSide neutralSeparated)

theorem heterogeneousLift_sibling (left : RichPortSystem GL) (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left)
    (neutralIndependent : GL.IsIndepSet ↑neutralSide)
    (falseIndependent : GL.IsIndepSet ↑falseSide)
    (trueIndependent : GL.IsIndepSet ↑trueSide)
    (neutralSeparated : ∀ point ∈ neutralSide,
      ¬ (footprint left false point ∧ footprint left true point)) :
    let result := heterogeneousLift left right neutralSide falseSide trueSide
      neutralIndependent falseIndependent trueIndependent neutralSeparated
    result.I = (liftRPS left right).I ∧ result.ports = (liftRPS left right).ports ∧
      result.ep = (liftRPS left right).ep ∧ result.side = (liftRPS left right).side := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem lift_footprint_neutral (left : RichPortSystem GL) (right : RichPortSystem GR)
    (point : Left × Right) (direction : Bool) (member : point.2 ∈ right.Xstar) :
    footprint (liftRPS left right) direction point ↔ footprint left direction point.1 := by
  have noFootprint : ¬ footprint right direction point.2 := by
    rintro ⟨parent, memberParent, confused⟩
    exact right.not_conflict_ep_of_mem_Xstar member direction memberParent confused
  have nearby : near GR right.Xstar point.2 := ⟨point.2, member, conflict_rfl _⟩
  rw [lift_footprint_iff]
  simp only [noFootprint, nearby, and_false, false_or, and_true]

theorem lift_footprint_side (left : RichPortSystem GL) (right : RichPortSystem GR)
    (point : Left × Right) (direction side : Bool) (member : point.2 ∈ right.Xc side) :
    footprint (liftRPS left right) direction point ↔
      direction = side ∧ near GL left.Xstar point.1 := by
  have noNeutral : point.2 ∉ right.Xstar := by
    intro memberNeutral
    cases side
    · exact (right.mem_Xstar.mp memberNeutral).2.1 member
    · exact (right.mem_Xstar.mp memberNeutral).2.2 member
  have noNearby : ¬ near GR right.Xstar point.2 := by
    rw [near_neutral_iff right (right.Xc_subset_X side member)]
    exact noNeutral
  have rightFootprint : footprint right direction point.2 ↔ direction = side := by
    constructor
    · intro foot
      by_contra different
      have opposite : direction = !side := by
        rcases bool_eq_or_eq_not direction side with same | opposite
        · exact False.elim (different same)
        · exact opposite
      have classMember := right.mem_Xc.mpr ⟨right.Xc_subset_X side member, foot⟩
      rw [opposite] at classMember
      exact right.notMem_Xc_of_mem_Xc member classMember
    · rintro rfl
      exact (right.mem_Xc.mp member).2
  rw [lift_footprint_iff, rightFootprint]
  constructor
  · rintro (⟨nearby, same⟩ | ⟨_, impossible⟩)
    · exact ⟨same, nearby⟩
    · exact False.elim (noNearby impossible)
  · rintro ⟨same, nearby⟩
    exact Or.inl ⟨nearby, same⟩

def auxiliaryFoot (left : RichPortSystem GL) (neutralSide : Finset Left)
    (direction : Bool) : Finset Left :=
  neutralSide.filter (footprint left direction)

def auxiliaryNeutral (left : RichPortSystem GL) (neutralSide : Finset Left) : Finset Left :=
  neutralSide.filter fun point => ¬ footprint left false point ∧ ¬ footprint left true point

def inside (left : RichPortSystem GL) (side : Finset Left) : Finset Left :=
  side.filter (near GL left.Xstar)

def outside (left : RichPortSystem GL) (side : Finset Left) : Finset Left :=
  side.filter fun point => ¬ near GL left.Xstar point

theorem heterogeneousLift_Xc (left : RichPortSystem GL) (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left)
    (neutralIndependent : GL.IsIndepSet ↑neutralSide)
    (falseIndependent : GL.IsIndepSet ↑falseSide)
    (trueIndependent : GL.IsIndepSet ↑trueSide)
    (neutralSeparated : ∀ point ∈ neutralSide,
      ¬ (footprint left false point ∧ footprint left true point)) (direction : Bool) :
    (heterogeneousLift left right neutralSide falseSide trueSide
      neutralIndependent falseIndependent trueIndependent neutralSeparated).Xc direction =
    (auxiliaryFoot left neutralSide direction ×ˢ right.Xstar) ∪
      (inside left (if direction then trueSide else falseSide) ×ˢ right.Xc direction) := by
  ext point
  rw [RichPortSystem.mem_Xc]
  change (point ∈ heterogeneousAux right neutralSide falseSide trueSide ∧
      footprint (liftRPS left right) direction point) ↔ _
  rw [mem_heterogeneousAux]
  simp only [Finset.mem_union, Finset.mem_product, auxiliaryFoot, inside, Finset.mem_filter]
  constructor
  · rintro ⟨memberNeutral | memberFalse | memberTrue, footprintMember⟩
    · exact Or.inl ⟨⟨memberNeutral.1,
        (lift_footprint_neutral left right point direction memberNeutral.2).mp footprintMember⟩,
        memberNeutral.2⟩
    · obtain ⟨same, nearby⟩ :=
        (lift_footprint_side left right point direction false memberFalse.2).mp footprintMember
      subst direction
      exact Or.inr ⟨⟨memberFalse.1, nearby⟩, memberFalse.2⟩
    · obtain ⟨same, nearby⟩ :=
        (lift_footprint_side left right point direction true memberTrue.2).mp footprintMember
      subst direction
      exact Or.inr ⟨⟨memberTrue.1, nearby⟩, memberTrue.2⟩
  · rintro (⟨⟨memberSide, footprintMember⟩, memberNeutral⟩ |
      ⟨⟨memberSide, nearby⟩, memberClass⟩)
    · exact ⟨Or.inl ⟨memberSide, memberNeutral⟩,
        (lift_footprint_neutral left right point direction memberNeutral).mpr footprintMember⟩
    · constructor
      · cases direction
        · exact Or.inr (Or.inl ⟨memberSide, memberClass⟩)
        · exact Or.inr (Or.inr ⟨memberSide, memberClass⟩)
      · exact (lift_footprint_side left right point direction direction memberClass).mpr ⟨rfl, nearby⟩

theorem heterogeneousLift_Xstar (left : RichPortSystem GL) (right : RichPortSystem GR)
    (neutralSide falseSide trueSide : Finset Left)
    (neutralIndependent : GL.IsIndepSet ↑neutralSide)
    (falseIndependent : GL.IsIndepSet ↑falseSide)
    (trueIndependent : GL.IsIndepSet ↑trueSide)
    (neutralSeparated : ∀ point ∈ neutralSide,
      ¬ (footprint left false point ∧ footprint left true point)) :
    (heterogeneousLift left right neutralSide falseSide trueSide
      neutralIndependent falseIndependent trueIndependent neutralSeparated).Xstar =
    (auxiliaryNeutral left neutralSide ×ˢ right.Xstar) ∪
      (outside left falseSide ×ˢ right.Xc false) ∪
      (outside left trueSide ×ˢ right.Xc true) := by
  ext point
  rw [RichPortSystem.mem_Xstar]
  change (point ∈ heterogeneousAux right neutralSide falseSide trueSide ∧
      point ∉ (heterogeneousLift left right neutralSide falseSide trueSide
        neutralIndependent falseIndependent trueIndependent neutralSeparated).Xc false ∧
      point ∉ (heterogeneousLift left right neutralSide falseSide trueSide
        neutralIndependent falseIndependent trueIndependent neutralSeparated).Xc true) ↔ _
  have classMembership (direction : Bool) :
      point ∈ (heterogeneousLift left right neutralSide falseSide trueSide
        neutralIndependent falseIndependent trueIndependent neutralSeparated).Xc direction ↔
      point ∈ heterogeneousAux right neutralSide falseSide trueSide ∧
        footprint (liftRPS left right) direction point :=
    (heterogeneousLift left right neutralSide falseSide trueSide
      neutralIndependent falseIndependent trueIndependent neutralSeparated).mem_Xc
  rw [classMembership false, classMembership true]
  simp only [Finset.mem_union, Finset.mem_product, auxiliaryNeutral, outside, Finset.mem_filter]
  constructor
  · rintro ⟨member, noFalse, noTrue⟩
    have noFalseFoot : ¬ footprint (liftRPS left right) false point :=
      fun foot => noFalse ⟨member, foot⟩
    have noTrueFoot : ¬ footprint (liftRPS left right) true point :=
      fun foot => noTrue ⟨member, foot⟩
    rcases (mem_heterogeneousAux right neutralSide falseSide trueSide point).mp member with
      memberNeutral | memberFalse | memberTrue
    · exact Or.inl (Or.inl ⟨⟨memberNeutral.1,
        fun foot => noFalseFoot ((lift_footprint_neutral left right point false memberNeutral.2).mpr foot),
        fun foot => noTrueFoot ((lift_footprint_neutral left right point true memberNeutral.2).mpr foot)⟩,
        memberNeutral.2⟩)
    · exact Or.inl (Or.inr ⟨⟨memberFalse.1,
        fun nearby => noFalseFoot ((lift_footprint_side left right point false false memberFalse.2).mpr ⟨rfl, nearby⟩)⟩,
        memberFalse.2⟩)
    · exact Or.inr ⟨⟨memberTrue.1,
        fun nearby => noTrueFoot ((lift_footprint_side left right point true true memberTrue.2).mpr ⟨rfl, nearby⟩)⟩,
        memberTrue.2⟩
  · rintro ((⟨⟨memberSide, noFalse, noTrue⟩, memberNeutral⟩ |
      ⟨⟨memberSide, noNearby⟩, memberFalse⟩) | ⟨⟨memberSide, noNearby⟩, memberTrue⟩)
    · refine ⟨(mem_heterogeneousAux right neutralSide falseSide trueSide point).mpr
        (Or.inl ⟨memberSide, memberNeutral⟩), ?_, ?_⟩
      · rintro ⟨_, foot⟩
        exact noFalse ((lift_footprint_neutral left right point false memberNeutral).mp foot)
      · rintro ⟨_, foot⟩
        exact noTrue ((lift_footprint_neutral left right point true memberNeutral).mp foot)
    · refine ⟨(mem_heterogeneousAux right neutralSide falseSide trueSide point).mpr
        (Or.inr (Or.inl ⟨memberSide, memberFalse⟩)), ?_, ?_⟩
      · rintro ⟨_, foot⟩
        exact noNearby ((lift_footprint_side left right point false false memberFalse).mp foot).2
      · rintro ⟨_, foot⟩
        have impossible := ((lift_footprint_side left right point true false memberFalse).mp foot).1
        cases impossible
    · refine ⟨(mem_heterogeneousAux right neutralSide falseSide trueSide point).mpr
        (Or.inr (Or.inr ⟨memberSide, memberTrue⟩)), ?_, ?_⟩
      · rintro ⟨_, foot⟩
        have impossible := ((lift_footprint_side left right point false true memberTrue).mp foot).1
        cases impossible
      · rintro ⟨_, foot⟩
        exact noNearby ((lift_footprint_side left right point true true memberTrue).mp foot).2

def gao (left : RichPortSystem GL) (right : RichPortSystem GR) :
    RichPortSystem (strongProd GL GR) := liftRPS left (flip right)

def heterogeneousGao (left : RichPortSystem GL) (right : RichPortSystem GR)
    (neutralSide hSide vSide : Finset Left)
    (neutralIndependent : GL.IsIndepSet ↑neutralSide)
    (hIndependent : GL.IsIndepSet ↑hSide)
    (vIndependent : GL.IsIndepSet ↑vSide)
    (neutralSeparated : ∀ point ∈ neutralSide,
      ¬ (footprint left false point ∧ footprint left true point)) :
    RichPortSystem (strongProd GL GR) :=
  heterogeneousLift left (flip right) neutralSide hSide vSide
    neutralIndependent hIndependent vIndependent neutralSeparated

omit [DecidableEq Left] in
theorem sibling_admissible (host sibling : RichPortSystem GL)
    (samePorts : host.ports = sibling.ports) (sameEndpoints : host.ep = sibling.ep) :
    ∀ point ∈ sibling.X, ¬ (footprint host false point ∧ footprint host true point) := by
  intro point member both
  apply sibling.hsep point member
  simpa only [footprint, samePorts, sameEndpoints] using both

theorem sibling_auxiliaryFoot (host sibling : RichPortSystem GL)
    (samePorts : host.ports = sibling.ports) (sameEndpoints : host.ep = sibling.ep)
    (direction : Bool) : auxiliaryFoot host sibling.X direction = sibling.Xc direction := by
  ext point
  simp only [auxiliaryFoot, Finset.mem_filter, RichPortSystem.mem_Xc, footprint,
    samePorts, sameEndpoints]

theorem sibling_auxiliaryNeutral (host sibling : RichPortSystem GL)
    (samePorts : host.ports = sibling.ports) (sameEndpoints : host.ep = sibling.ep) :
    auxiliaryNeutral host sibling.X = sibling.Xstar := by
  ext point
  simp only [auxiliaryNeutral, Finset.mem_filter, RichPortSystem.mem_Xstar,
    RichPortSystem.mem_Xc, footprint, samePorts, sameEndpoints]
  constructor
  · rintro ⟨member, noFalse, noTrue⟩
    exact ⟨member, fun both => noFalse both.2, fun both => noTrue both.2⟩
  · rintro ⟨member, noFalse, noTrue⟩
    exact ⟨member, fun nearby => noFalse ⟨member, nearby⟩,
      fun nearby => noTrue ⟨member, nearby⟩⟩

end ShannonBounds.C7Improvement
