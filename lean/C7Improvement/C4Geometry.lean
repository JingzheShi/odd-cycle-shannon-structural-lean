import C7Improvement.C4Atoms

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

attribute [local simp] Fin.coe_ofNat_eq_mod

attribute [local irreducible] BaseC7.base G10 G10A G15X G15AX G15Ahet G15het L30 Jplus

def piece15Set (piece : Fin 13 × Fin 8) := tenAtomSet piece.1 ×ˢ fiveAtomSet piece.2

def pieces15Set (pieces : List (Fin 13 × Fin 8)) :=
  (pieces.map piece15Set).foldr (fun first second => first ∪ second) ∅

theorem G15het_family_pieces (letter : Letter) : G15het.fam letter =
    pieces15Set (fifteenPieces letter) := by
  cases letter
  · rw [RichPortSystem.fam, G15het_sibling.1, G15het_sibling.2.1, G15X, ← RichPortSystem.fam,
      gao_core_blocks]
    rfl
  · rw [RichPortSystem.fam, G15het, heterogeneousGao_Xstar,
      sibling_auxiliaryNeutral G10 G10 rfl rfl]
    simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, fifteenPieces, pieces15Set, piece15Set, tenAtomSet, fiveAtomSet,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty,
      RichPortSystem.fam, Finset.union_assoc]
  · rw [RichPortSystem.fam, G15het, heterogeneousGao_Xc,
      sibling_auxiliaryFoot G10 G10 rfl rfl false]
    simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, fifteenPieces, pieces15Set, piece15Set, tenAtomSet, fiveAtomSet,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty,
      RichPortSystem.fam, Bool.false_eq_true, ite_false, Bool.not_false]
  · rw [RichPortSystem.fam, G15het, heterogeneousGao_Xc,
      sibling_auxiliaryFoot G10 G10 rfl rfl true]
    simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, fifteenPieces, pieces15Set, piece15Set, tenAtomSet, fiveAtomSet,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty,
      RichPortSystem.fam, ite_true, Bool.not_true]
  · rw [RichPortSystem.fam, G15het_sibling.2.1, G15X, gao_ports]
    simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, fifteenPieces, pieces15Set, piece15Set, tenAtomSet, fiveAtomSet,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty,
      RichPortSystem.fam, Finset.empty_union, Finset.union_comm]
  · change transversal G15het true = _
    change G15het.ports.image (G15het.ep true) = _
    rw [G15het_sibling.2.1, G15het_sibling.2.2.1]
    change transversal G15X true = _
    rw [G15X, gao_transversal]
    simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, fifteenPieces, pieces15Set, piece15Set, tenAtomSet, fiveAtomSet,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty,
      RichPortSystem.fam, transversal, Bool.not_true, Finset.empty_union, Finset.union_comm]
  · change G15het.ports.image (G15het.ep false) = _
    rw [G15het_sibling.2.1, G15het_sibling.2.2.1]
    change transversal G15X false = _
    rw [G15X, gao_transversal]
    simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, fifteenPieces, pieces15Set, piece15Set, tenAtomSet, fiveAtomSet,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty,
      RichPortSystem.fam, transversal, Bool.not_false, Finset.empty_union, Finset.union_comm]

theorem gao_rest {Left Right : Type*} [DecidableEq Left] [DecidableEq Right]
    {GL : SimpleGraph Left} {GR : SimpleGraph Right}
    [DecidableRel GL.Adj] [DecidableRel GR.Adj]
    (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao left right).X \ (gao left right).Xstar =
      ((left.X \ left.Xstar) ×ˢ right.Xstar) ∪ (left.Xstar ×ˢ (right.X \ right.Xstar)) := by
  rw [rest_eq_classes, gao_Xc, gao_Xc, rest_eq_classes left, rest_eq_classes right]
  simp only [Bool.not_true, Bool.not_false, Finset.product_union, Finset.union_product,
    Finset.empty_union, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]

theorem G15AX_neutral_pieces : G15AX.Xstar = pieces15Set [(1,1), (7,7)] := by
  rw [G15AX_neutral, G15X, gao_Xstar]
  simp only [pieces15Set, piece15Set, tenAtomSet, fiveAtomSet, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty, RichPortSystem.fam]

theorem G15AX_rest_pieces : G15AX.X \ G15AX.Xstar = pieces15Set [(7,1), (1,7)] := by
  rw [G15AX, gao_rest, G10A_X, G10A_neutral]
  simp only [pieces15Set, piece15Set, tenAtomSet, fiveAtomSet, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty, RichPortSystem.fam]

theorem G15Ahet_neutral_pieces : G15Ahet.Xstar = pieces15Set [(1,1), (9,3), (7,2)] := by
  rw [G15Ahet, heterogeneousGao_Xstar, sibling_auxiliaryNeutral G10A G10A rfl rfl,
    G10A_neutral, own_outside, G10A_X, G10A_neutral]
  have commonOutside : outside G10A Jplus = outside G10 Jplus := by
    simp only [outside, G10A_neutral]
  rw [commonOutside]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, pieces15Set, piece15Set, tenAtomSet, fiveAtomSet, RichPortSystem.fam,
    List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty,
    Finset.union_assoc]

theorem G15Ahet_rest_pieces : G15Ahet.X \ G15Ahet.Xstar =
    pieces15Set [(11,1), (1,2), (12,1), (10,3)] := by
  rw [rest_eq_classes, G15Ahet, heterogeneousGao_Xc, heterogeneousGao_Xc,
    sibling_auxiliaryFoot G10A G10A rfl rfl false,
    sibling_auxiliaryFoot G10A G10A rfl rfl true]
  simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false, Bool.not_true]
  rw [inside_own, G10A_neutral]
  have commonInside : inside G10A Jplus = inside G10 Jplus := by
    simp only [inside, G10A_neutral]
  rw [commonInside]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, pieces15Set, piece15Set, tenAtomSet, fiveAtomSet, RichPortSystem.fam,
    List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Finset.union_empty,
    Finset.empty_union, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]

def piece30Set (piece : (Fin 13 × Fin 8) × (Fin 13 × Fin 8)) :=
  piece15Set piece.1 ×ˢ piece15Set piece.2

def pieces30Set (pieces : List ((Fin 13 × Fin 8) × (Fin 13 × Fin 8))) :=
  (pieces.map piece30Set).foldr (fun first second => first ∪ second) ∅

theorem fold_union_append {Point : Type*} [DecidableEq Point]
    (first second : List (Finset Point)) :
    (first ++ second).foldr (fun first second => first ∪ second) ∅ =
      first.foldr (fun first second => first ∪ second) ∅ ∪
        second.foldr (fun first second => first ∪ second) ∅ := by
  induction first with
  | nil => simp
  | cons points first inductionHypothesis =>
    simp only [List.cons_append, List.foldr_cons, inductionHypothesis, Finset.union_assoc]

theorem pieces30_append (first second : List ((Fin 13 × Fin 8) × (Fin 13 × Fin 8))) :
    pieces30Set (first ++ second) = pieces30Set first ∪ pieces30Set second := by
  simp only [pieces30Set, List.map_append, fold_union_append]

theorem pieces_single_cross (piece : Fin 13 × Fin 8) (right : List (Fin 13 × Fin 8)) :
    piece15Set piece ×ˢ pieces15Set right =
      pieces30Set (right.map fun other => (piece, other)) := by
  induction right with
  | nil => simp [pieces15Set, pieces30Set]
  | cons other right inductionHypothesis =>
    change piece15Set piece ×ˢ (piece15Set other ∪ pieces15Set right) =
      piece30Set (piece, other) ∪ pieces30Set (right.map fun other => (piece, other))
    rw [Finset.product_union, inductionHypothesis]
    rfl

theorem pieces_cross (left right : List (Fin 13 × Fin 8)) :
    pieces15Set left ×ˢ pieces15Set right = pieces30Set (crossPieces left right) := by
  induction left with
  | nil => simp [pieces15Set, pieces30Set, crossPieces]
  | cons piece left inductionHypothesis =>
    change (piece15Set piece ∪ pieces15Set left) ×ˢ pieces15Set right =
      pieces30Set ((right.map fun other => (piece, other)) ++ crossPieces left right)
    rw [Finset.union_product, inductionHypothesis, pieces_single_cross, pieces30_append]

theorem L30_neutral_pieces : L30.Xstar = pieces30Set C4reference := by
  rw [L30, gao_Xstar, flip_Xstar]
  change (G15AX.Xstar ×ˢ G15Ahet.Xstar) ∪
    ((G15AX.X \ G15AX.Xstar) ×ˢ (G15Ahet.X \ G15Ahet.Xstar)) = _
  rw [G15AX_rest_pieces, G15Ahet_rest_pieces, G15AX_neutral_pieces,
    G15Ahet_neutral_pieces, pieces_cross, pieces_cross, C4reference, pieces30_append]

end ShannonBounds.C7Improvement
