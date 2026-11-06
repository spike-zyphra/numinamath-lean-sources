import Mathlib

theorem inequalities_33144 (x y z : ℝ) (h₀ : x^2 + y^2 + z = 15) (h₁ : x + y + z^2 = 27)
    (h₂ : x * y + y * z + z * x = 7) :
    7 ≤ |x + y + z| ∧ |x + y + z| ≤ 8 := by

  have h3 : (x + y + z) ^ 2 + (x + y + z) - 56 = 0 := by
    nlinarith

  have h4 : (x + y + z - 7) * (x + y + z + 8) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where x + y + z = 7, so |x + y + z| = 7 and 7 ≤ 7 ≤ 8.
    have h7 : x + y + z = 7 := by linarith
    constructor
    · -- Show 7 ≤ |x + y + z|
      rw [h7]
      norm_num [abs_of_nonneg]
    · -- Show |x + y + z| ≤ 8
      rw [h7]
      norm_num [abs_of_nonneg]
  · -- Case where x + y + z = -8, so |x + y + z| = 8 and 7 ≤ 8 ≤ 8.
    have h8 : x + y + z = -8 := by linarith
    constructor
    · -- Show 7 ≤ |x + y + z|
      rw [h8]
      norm_num [abs_of_nonpos]
    · -- Show |x + y + z| ≤ 8
      rw [h8]
      norm_num [abs_of_nonpos]