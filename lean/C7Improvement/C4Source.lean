import C7Improvement.C4Geometry

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 10000
set_option maxHeartbeats 400000

attribute [local irreducible] BaseC7.base G10 G15X G15het sourceJ30

theorem gao_I_family_fold {Left Right : Type*} [Fintype Left] [Fintype Right]
    [DecidableEq Left] [DecidableEq Right] {GL : SimpleGraph Left} {GR : SimpleGraph Right}
    [DecidableRel GL.Adj] [DecidableRel GR.Adj]
    (left : RichPortSystem GL) (right : RichPortSystem GR) :
    (gao left right).I =
      (mainBlockLetters.map fun letters => left.fam letters.1 ×ˢ right.fam letters.2).foldr
        (fun first second => first ∪ second) ∅ := by
  rw [gao_I_blocks]
  rfl

theorem pieces30_flatMap {Key : Type*} (keys : List Key)
    (pieces : Key → List ((Fin 13 × Fin 8) × (Fin 13 × Fin 8))) :
    pieces30Set (keys.flatMap pieces) = (keys.map fun key => pieces30Set (pieces key)).foldr
      (fun first second => first ∪ second) ∅ := by
  induction keys with
  | nil => simp [pieces30Set]
  | cons key keys inductionHypothesis =>
    rw [List.flatMap_cons, pieces30_append, inductionHypothesis]
    rfl

theorem sourceJ30_I_pieces : sourceJ30.I = pieces30Set C4source := by
  rw [sourceJ30, gao_I_family_fold, C4source, pieces30_flatMap]
  simp only [G15het_family_pieces, pieces_cross]

def transformThirty (point : ((BaseC7.Code × BaseC7.Code) × BaseC7.Code) ×
    ((BaseC7.Code × BaseC7.Code) × BaseC7.Code)) :=
  (transformTriple point.1, transformTriple point.2)

theorem transformThirty_eq : transformThirty = Prod.map transformTriple transformTriple := rfl

theorem transformTriple_eq : transformTriple = Prod.map transformPair transform := rfl

theorem transformThirty_injective : Function.Injective transformThirty := by
  intro first second equal
  exact Prod.ext (transformTriple_injective (congrArg Prod.fst equal))
    (transformTriple_injective (congrArg Prod.snd equal))

theorem transformThirty_conflict (first second : ((BaseC7.Code × BaseC7.Code) × BaseC7.Code) ×
    ((BaseC7.Code × BaseC7.Code) × BaseC7.Code)) :
    conflict (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5))
      (transformThirty first) (transformThirty second) ↔
    conflict (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5))
      first second := by
  simp only [transformThirty, transformTriple, transformPair, conflict_strongProd_iff, transform_conflict]

def J30 := sourceJ30.I.image transformThirty

theorem J30_independent :
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5)).IsIndepSet ↑J30 := by
  intro first memberFirst second memberSecond unequal adjacent
  obtain ⟨sourceFirst, memberSourceFirst, rfl⟩ := Finset.mem_image.mp memberFirst
  obtain ⟨sourceSecond, memberSourceSecond, rfl⟩ := Finset.mem_image.mp memberSecond
  exact not_conflict_of_indep sourceJ30.hI memberSourceFirst memberSourceSecond
    (fun equal => unequal (congrArg transformThirty equal))
    ((transformThirty_conflict sourceFirst sourceSecond).mp (Or.inr adjacent))

theorem J30_card : J30.card = 2455726444728097 := by
  rw [J30, Finset.card_image_of_injective _ transformThirty_injective]
  change sourceJ30.N = _
  rw [sourceJ30, gao_N, G15het_profile.1, G15het_profile.2.1, G15het_profile.2.2.1]

def C4blocks := C4source.map fun piece => (piece30Set piece).image transformThirty

theorem J30_eq_blocks : J30 = C4blocks.foldr (fun first second => first ∪ second) ∅ := by
  rw [J30, sourceJ30_I_pieces, pieces30Set, image_fold_union]
  simp only [C4blocks, List.map_map, Function.comp_def]

theorem transformed_piece_eq (piece : (Fin 13 × Fin 8) × (Fin 13 × Fin 8)) :
    (piece30Set piece).image transformThirty =
      (((tenAtomList piece.1.1).map transformPair).toFinset ×ˢ
        ((fiveAtomList piece.1.2).map transform).toFinset) ×ˢ
      (((tenAtomList piece.2.1).map transformPair).toFinset ×ˢ
        ((fiveAtomList piece.2.2).map transform).toFinset) := by
  simp only [piece30Set, piece15Set, transformThirty, transformTriple,
    ← tenAtomList_eq, ← fiveAtomList_eq, list_map_finset]
  rw [transformThirty_eq, Finset.prodMap_image_product transformTriple transformTriple]
  rw [transformTriple_eq, Finset.prodMap_image_product transformPair transform,
    Finset.prodMap_image_product transformPair transform]

end ShannonBounds.C7Improvement
