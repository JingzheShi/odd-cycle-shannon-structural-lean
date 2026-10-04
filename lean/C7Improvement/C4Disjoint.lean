import C7Improvement.CardTotalDisjoint
import C7Improvement.C4SizeData

namespace ShannonBounds.C7Improvement

attribute [local irreducible] BaseC7.base G10 G15het sourceJ30 J30 C4source C4blocks

theorem fiveAtomSet_card_length (atom : Fin 8) : (fiveAtomSet atom).card = (fiveAtomList atom).length := by
  rw [← fiveAtomList_eq, List.toFinset_card_of_nodup (fiveAtom_nodup atom)]

theorem C4_piece_card (piece : (Fin 13 × Fin 8) × (Fin 13 × Fin 8)) :
    ((piece30Set piece).image transformThirty).card =
      (tenAtomSize piece.1.1 * (fiveAtomList piece.1.2).length) *
        (tenAtomSize piece.2.1 * (fiveAtomList piece.2.2).length) := by
  rw [Finset.card_image_of_injective _ transformThirty_injective]
  simp only [piece30Set, piece15Set, Finset.card_product, tenAtomSet_card, fiveAtomSet_card_length]

theorem C4_block_card_sum : (C4blocks.map Finset.card).sum = 2455726444728097 := by
  have equal : (C4blocks.map Finset.card).sum = (C4source.map fun piece =>
      (tenAtomSize piece.1.1 * (fiveAtomList piece.1.2).length) *
        (tenAtomSize piece.2.1 * (fiveAtomList piece.2.2).length)).sum := by
    rw [C4blocks, List.map_map]
    exact mapped_sum_equal C4source _ _ (fun piece _ => C4_piece_card piece)
  exact equal.trans C4_size_sum_check

theorem C4blocks_disjoint : C4blocks.Pairwise Disjoint := by
  apply pairwise_disjoint_of_card_total
  calc
    _ = J30.card := by rw [J30_eq_blocks]
    _ = 2455726444728097 := J30_card
    _ = (C4blocks.map Finset.card).sum := C4_block_card_sum.symm

end ShannonBounds.C7Improvement
