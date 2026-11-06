import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_19878 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ t = ((y - x)^2 / ((y - z) * (z - x)) +
    (z - y)^2 / ((z - x) * (x - y)) + (x - z)^2 / ((x - y) * (y - z)))} 3 := by

  constructor
  · -- Show 3 is in the set
    use 0, 1, 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
  · -- Show no value smaller than 3 is in the set
    intro t
    rintro ⟨x, y, z, h1, h2, h3, ht⟩
    have h4 : ((y - x) ^ 2 / ((y - z) * (z - x)) + (z - y) ^ 2 / ((z - x) * (x - y)) + (x - z) ^ 2 / ((x - y) * (y - z)) ) = 3 := by
      have h5 : x - y ≠ 0 := by
        intro h
        apply h1
        linarith
      have h6 : y - z ≠ 0 := by
        intro h
        apply h2
        linarith
      have h7 : z - x ≠ 0 := by
        intro h
        apply h3
        linarith
      field_simp [(show y - z ≠ 0 by exact h6), (show z - x ≠ 0 by exact h7), (show x - y ≠ 0 by exact h5)]
      ring
    have ht' : t = ((y - x) ^ 2 / ((y - z) * (z - x)) + (z - y) ^ 2 / ((z - x) * (x - y)) + (x - z) ^ 2 / ((x - y) * (y - z)) ) := by
      linarith
    rw [ht']
    linarith [h4]