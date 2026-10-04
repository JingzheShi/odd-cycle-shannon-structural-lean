import C7Improvement.Atoms10Bridge
import C7Improvement.C2Data
import C7Improvement.BlockDisjoint
import C7Improvement.G15

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 10000
set_option maxHeartbeats 300000
set_option Elab.async false

attribute [local irreducible] BaseC7.base G10 G15X

def transformTriple (point : (BaseC7.Code × BaseC7.Code) × BaseC7.Code) :=
  (transformPair point.1, transform point.2)

theorem transformTriple_injective : Function.Injective transformTriple := by
  intro first second equal
  exact Prod.ext (transformPair_injective (congrArg Prod.fst equal))
    (transformEquiv.injective (congrArg Prod.snd equal))

theorem transformTriple_conflict (first second : (BaseC7.Code × BaseC7.Code) × BaseC7.Code) :
    conflict (strongProd (strongProd G5 G5) G5) (transformTriple first) (transformTriple second) ↔
      conflict (strongProd (strongProd G5 G5) G5) first second := by
  simp only [conflict_strongProd_iff, transformTriple, transformPair, transform_conflict]

def J15 : Finset ((BaseC7.Code × BaseC7.Code) × BaseC7.Code) := G15X.I.image transformTriple

theorem J15_independent : (strongProd (strongProd G5 G5) G5).IsIndepSet ↑J15 := by
  intro first memberFirst second memberSecond unequal adjacent
  obtain ⟨sourceFirst, memberSourceFirst, rfl⟩ := Finset.mem_image.mp memberFirst
  obtain ⟨sourceSecond, memberSourceSecond, rfl⟩ := Finset.mem_image.mp memberSecond
  exact not_conflict_of_indep G15X.hI memberSourceFirst memberSourceSecond
    (fun equal => unequal (congrArg transformTriple equal))
    ((transformTriple_conflict sourceFirst sourceSecond).mp (Or.inr adjacent))

theorem J15_card : J15.card = G15X.N := by
  rw [J15, Finset.card_image_of_injective _ transformTriple_injective]
  rfl

theorem list_map_finset {Point Target : Type*} [DecidableEq Point] [DecidableEq Target]
    (points : List Point) (mapping : Point → Target) :
    (points.map mapping).toFinset = points.toFinset.image mapping := by
  ext point
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

theorem transformed_block_eq (letters : Letter × Letter) :
    (G10.fam letters.1 ×ˢ BaseC7.base.fam letters.2).image transformTriple =
      (transformed10Atom letters.1).toFinset ×ˢ (transformed5Atom letters.2).toFinset := by
  rw [transformed10Atom, transformed5Atom, list_map_finset, list_map_finset,
    atom10_eq, baseAtom_eq]
  exact Finset.prodMap_image_product transformPair transform _ _

def J15blocks : List (Finset ((BaseC7.Code × BaseC7.Code) × BaseC7.Code)) :=
  mainBlockLetters.map fun letters =>
    (G10.fam letters.1 ×ˢ BaseC7.base.fam letters.2).image transformTriple

theorem image_fold_union {Point Target : Type*} [DecidableEq Point] [DecidableEq Target]
    (sets : List (Finset Point)) (mapping : Point → Target) :
    (sets.foldr (fun first second => first ∪ second) ∅).image mapping =
      ((sets.map fun points => points.image mapping).foldr
        (fun first second => first ∪ second) ∅) := by
  induction sets with
  | nil => simp
  | cons points sets inductionHypothesis =>
    simp only [List.foldr_cons, List.map_cons, Finset.image_union, inductionHypothesis]

theorem G15X_I_families : G15X.I =
    (mainBlockLetters.map fun letters => G10.fam letters.1 ×ˢ BaseC7.base.fam letters.2).foldr
      (fun first second => first ∪ second) ∅ := by
  rw [G15X, gao_I_blocks]
  rfl

theorem J15_eq_blocks : J15 = J15blocks.foldr (fun first second => first ∪ second) ∅ := by
  rw [J15, G15X_I_families, image_fold_union]
  simp only [List.map_map, Function.comp_def, J15blocks]

theorem J15blocks_disjoint : J15blocks.Pairwise Disjoint := by
  rw [J15blocks, List.pairwise_map]
  exact mainBlockLetters_separated.imp fun {first second} separated =>
    (Finset.disjoint_image transformTriple_injective).mpr
      (separated_products_disjoint G10 BaseC7.base first second separated)

end ShannonBounds.C7Improvement
