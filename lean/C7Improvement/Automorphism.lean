import ShannonBounds.BaseC7Data

namespace ShannonBounds.C7Improvement

open BaseC7

def transform (point : BaseC7.Code) : BaseC7.Code :=
  ⟨(9 - dgt 7 point) % 7 + 7 * dgt 343 point + 49 * dgt 1 point +
      343 * ((9 - dgt 49 point) % 7) + 2401 * dgt 2401 point, by
    have first : (9 - dgt 7 point) % 7 < 7 := Nat.mod_lt _ (by decide)
    have second := dgt_lt 343 point
    have third := dgt_lt 1 point
    have fourth : (9 - dgt 49 point) % 7 < 7 := Nat.mod_lt _ (by decide)
    have fifth := dgt_lt 2401 point
    omega⟩

def inverseTransform (point : BaseC7.Code) : BaseC7.Code :=
  ⟨dgt 49 point + 7 * ((9 - dgt 1 point) % 7) + 49 * ((9 - dgt 343 point) % 7) +
      343 * dgt 7 point + 2401 * dgt 2401 point, by
    have first := dgt_lt 49 point
    have second : (9 - dgt 1 point) % 7 < 7 := Nat.mod_lt _ (by decide)
    have third : (9 - dgt 343 point) % 7 < 7 := Nat.mod_lt _ (by decide)
    have fourth := dgt_lt 7 point
    have fifth := dgt_lt 2401 point
    omega⟩

theorem transform_inverse_check :
    ∀ point : BaseC7.Code, inverseTransform (transform point) = point ∧
      transform (inverseTransform point) = point := by native_decide

theorem transform_coordinate_check : ∀ point : BaseC7.Code,
    dgt 1 (transform point) = (9 - dgt 7 point) % 7 ∧
    dgt 7 (transform point) = dgt 343 point ∧
    dgt 49 (transform point) = dgt 1 point ∧
    dgt 343 (transform point) = (9 - dgt 49 point) % 7 ∧
    dgt 2401 (transform point) = dgt 2401 point := by native_decide

theorem reflection_preserves : ∀ first < 7, ∀ second < 7,
    sconf ((9 - first) % 7) ((9 - second) % 7) = sconf first second := by native_decide

theorem transform_wconf (first second : BaseC7.Code) :
    wconf (transform first) (transform second) = wconf first second := by
  obtain ⟨firstOne, firstTwo, firstThree, firstFour, firstFive⟩ := transform_coordinate_check first
  obtain ⟨secondOne, secondTwo, secondThree, secondFour, secondFive⟩ := transform_coordinate_check second
  unfold wconf
  rw [firstOne, firstTwo, firstThree, firstFour, firstFive,
    secondOne, secondTwo, secondThree, secondFour, secondFive,
    reflection_preserves (dgt 7 first) (dgt_lt 7 first) (dgt 7 second) (dgt_lt 7 second),
    reflection_preserves (dgt 49 first) (dgt_lt 49 first) (dgt 49 second) (dgt_lt 49 second)]
  simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

def transformEquiv : BaseC7.Code ≃ BaseC7.Code where
  toFun := transform
  invFun := inverseTransform
  left_inv point := (transform_inverse_check point).1
  right_inv point := (transform_inverse_check point).2

theorem transform_conflict (first second : BaseC7.Code) :
    conflict G5 (transform first) (transform second) ↔ conflict G5 first second := by
  rw [conflict_G5, conflict_G5, transform_wconf]

def transformGraphIso : G5 ≃g G5 where
  toEquiv := transformEquiv
  map_rel_iff' := by
    intro first second
    change (transform first ≠ transform second ∧ wconf (transform first) (transform second) = true) ↔
      (first ≠ second ∧ wconf first second = true)
    rw [transform_wconf]
    constructor
    · rintro ⟨unequal, confused⟩
      exact ⟨fun equal => unequal (congrArg transform equal), confused⟩
    · rintro ⟨unequal, confused⟩
      exact ⟨fun equal => unequal (transformEquiv.injective equal), confused⟩

def transformPair (point : BaseC7.Code × BaseC7.Code) : BaseC7.Code × BaseC7.Code :=
  (transform point.1, transform point.2)

theorem transformPair_conflict (first second : BaseC7.Code × BaseC7.Code) :
    conflict (strongProd G5 G5) (transformPair first) (transformPair second) ↔
      conflict (strongProd G5 G5) first second := by
  rw [conflict_strongProd_iff, conflict_strongProd_iff]
  exact and_congr (transform_conflict first.1 second.1) (transform_conflict first.2 second.2)

end ShannonBounds.C7Improvement
