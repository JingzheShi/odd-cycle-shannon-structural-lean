import C7Improvement.ExplicitLift

namespace ShannonBounds.C7Improvement

open BaseC7

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem bool_neg_true (flag : Bool) : (!flag) = true ↔ ¬ flag = true := by
  cases flag <;> decide

def baseAtom : Letter → List BaseC7.Code
  | .B => Ilist.filter fun point => !(portsList.contains point)
  | .N => Xlist.filter fun point => !(fpB false point || fpB true point)
  | .A => Xlist.filter (fpB false)
  | .D => Xlist.filter (fpB true)
  | .O => portsList
  | .H => portsList.map (bep true)
  | .V => portsList.map (bep false)

theorem baseAtom_eq (letter : Letter) : (baseAtom letter).toFinset = BaseC7.base.fam letter := by
  cases letter
  · change (Ilist.filter fun point => !(portsList.contains point)).toFinset = Iset \ portsSet
    ext point
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_sdiff,
      mem_Iset, mem_portsSet, bool_neg_true, List.contains_iff_mem]
  · change (Xlist.filter fun point => !(fpB false point || fpB true point)).toFinset = BaseC7.base.Xstar
    ext point
    rw [RichPortSystem.mem_Xstar, Xc_eq, Xc_eq]
    change (point ∈ (Xlist.filter fun point => !(fpB false point || fpB true point)).toFinset) ↔
      point ∈ Xset ∧ point ∉ BaseC7.Xc false ∧ point ∉ BaseC7.Xc true
    simp only [List.mem_toFinset, List.mem_filter, BaseC7.mem_Xc, mem_Xset,
      bool_neg_true, Bool.or_eq_true, not_or]
    constructor
    · rintro ⟨member, noFalse, noTrue⟩
      exact ⟨member, fun both => noFalse both.2, fun both => noTrue both.2⟩
    · rintro ⟨member, noFalse, noTrue⟩
      exact ⟨member, fun nearby => noFalse ⟨member, nearby⟩,
        fun nearby => noTrue ⟨member, nearby⟩⟩
  · change (Xlist.filter (fpB false)).toFinset = BaseC7.base.Xc false
    rw [Xc_eq]
    ext point
    simp only [List.mem_toFinset, List.mem_filter, BaseC7.mem_Xc]
  · change (Xlist.filter (fpB true)).toFinset = BaseC7.base.Xc true
    rw [Xc_eq]
    ext point
    simp only [List.mem_toFinset, List.mem_filter, BaseC7.mem_Xc]
  · change portsList.toFinset = portsSet
    ext point
    simp only [List.mem_toFinset, mem_portsSet]
  · change (portsList.map (bep true)).toFinset = portsSet.image (bep true)
    ext point
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, mem_portsSet]
  · change (portsList.map (bep false)).toFinset = portsSet.image (bep false)
    ext point
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, mem_portsSet]

def mainBlockLetters : List (Letter × Letter) :=
  [(.B, .B), (.O, .N), (.H, .D), (.V, .A), (.N, .O), (.D, .V), (.A, .H)]

def baseProductList (left right : Letter) : List (BaseC7.Code × BaseC7.Code) :=
  (baseAtom left).flatMap fun first => (baseAtom right).map fun second => (first, second)

def main10List : List (BaseC7.Code × BaseC7.Code) :=
  mainBlockLetters.flatMap fun letters => baseProductList letters.1 letters.2

theorem baseProductList_eq (left right : Letter) :
    (baseProductList left right).toFinset =
      BaseC7.base.fam left ×ˢ BaseC7.base.fam right := by
  rw [← baseAtom_eq left, ← baseAtom_eq right]
  ext point
  simp only [baseProductList, List.mem_toFinset, List.mem_flatMap, List.mem_map, Finset.mem_product]
  constructor
  · rintro ⟨first, memberFirst, second, memberSecond, equal⟩
    cases equal
    exact ⟨memberFirst, memberSecond⟩
  · rintro ⟨memberFirst, memberSecond⟩
    exact ⟨point.1, memberFirst, point.2, memberSecond, rfl⟩

theorem main10List_eq : main10List.toFinset = G10.I := by
  rw [G10, gao_I_blocks]
  simp only [main10List, mainBlockLetters, List.flatMap_cons, List.flatMap_nil,
    List.toFinset_append, baseProductList_eq, ordinaryBlocks, blockUnion,
    List.foldr_cons, List.foldr_nil, Finset.union_empty]
  rfl

end ShannonBounds.C7Improvement
