import C7Improvement.SparseCount

namespace ShannonBounds.C7Improvement

open scoped BigOperators

theorem frequency_product_pair {First Second FirstKey SecondKey : Type*}
    [DecidableEq First] [DecidableEq Second] [DecidableEq FirstKey] [DecidableEq SecondKey]
    (first : Finset First) (second : Finset Second)
    (firstTag : First → FirstKey) (secondTag : Second → SecondKey)
    (firstKey : FirstKey) (secondKey : SecondKey) :
    frequency (first ×ˢ second) (fun point => (firstTag point.1, secondTag point.2))
      (firstKey, secondKey) = frequency first firstTag firstKey * frequency second secondTag secondKey := by
  have equalFilters : (first ×ˢ second).filter
      (fun point => (firstTag point.1, secondTag point.2) = (firstKey, secondKey)) =
      (first.filter fun point => firstTag point = firstKey) ×ˢ
        (second.filter fun point => secondTag point = secondKey) := by
    ext point
    simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
    tauto
  simp only [frequency, equalFilters, Finset.card_product]

theorem four_histogram_count {First Second Third Fourth FirstKey SecondKey ThirdKey FourthKey : Type*}
    [DecidableEq First] [DecidableEq Second] [DecidableEq Third] [DecidableEq Fourth]
    [Fintype FirstKey] [Fintype SecondKey] [Fintype ThirdKey] [Fintype FourthKey]
    [DecidableEq FirstKey] [DecidableEq SecondKey] [DecidableEq ThirdKey] [DecidableEq FourthKey]
    (first : Finset First) (second : Finset Second) (third : Finset Third) (fourth : Finset Fourth)
    (firstTag : First → FirstKey) (secondTag : Second → SecondKey)
    (thirdTag : Third → ThirdKey) (fourthTag : Fourth → FourthKey)
    (accepted : FirstKey → SecondKey → ThirdKey → FourthKey → Bool) :
    (((first ×ˢ second) ×ˢ (third ×ˢ fourth)).filter fun point =>
      accepted (firstTag point.1.1) (secondTag point.1.2)
        (thirdTag point.2.1) (fourthTag point.2.2) = true).card =
    ∑ firstKey, ∑ secondKey, ∑ thirdKey, ∑ fourthKey,
      if accepted firstKey secondKey thirdKey fourthKey then
        frequency first firstTag firstKey * frequency second secondTag secondKey *
          frequency third thirdTag thirdKey * frequency fourth fourthTag fourthKey else 0 := by
  rw [Finset.card_filter]
  rw [histogram_product_sum_on (first ×ˢ second) (third ×ˢ fourth)
    (fun point => (firstTag point.1, secondTag point.2))
    (fun point => (thirdTag point.1, fourthTag point.2))
    (Finset.univ ×ˢ Finset.univ) (Finset.univ ×ˢ Finset.univ)
    (fun _ _ => Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (fun _ _ => Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (fun first second => (first, second))
    (fun keys => if accepted keys.1.1 keys.1.2 keys.2.1 keys.2.2 then 1 else 0)]
  simp only [Finset.sum_product, frequency_product_pair]
  apply Finset.sum_congr rfl
  intro firstKey firstMember
  apply Finset.sum_congr rfl
  intro secondKey secondMember
  apply Finset.sum_congr rfl
  intro thirdKey thirdMember
  apply Finset.sum_congr rfl
  intro fourthKey fourthMember
  split_ifs <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.mul_assoc]

end ShannonBounds.C7Improvement
