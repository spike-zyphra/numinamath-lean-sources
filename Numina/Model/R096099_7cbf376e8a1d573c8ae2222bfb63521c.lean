import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_597542 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 1 ∧ t = 1/x + 4/y + 9/z} 36 := by
  constructor
  · -- Show 36 is in the set
    use 1 / 6, 1 / 3, 1 / 2
    constructor
    · norm_num -- Show 1/6 > 0
    constructor
    · norm_num -- Show 1/3 > 0
    constructor
    · norm_num -- Show 1/2 > 0
    constructor
    · norm_num -- Show sum equals 1
    norm_num
  · -- Show 36 is a lower bound
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
    have h2 : 1 / x + 4 / y + 9 / z ≥ 36 := by
      have h3 : x * y * z > 0 := mul_pos (mul_pos hx hy) hz
      have h4 : 1 / x + 4 / y + 9 / z - 36 ≥ 0 := by
        have h5 : (1 / x + 4 / y + 9 / z - 36) = (y * z + 4 * x * z + 9 * x * y - 36 * x * y * z) / (x * y * z) := by
          field_simp
          ring
        rw [h5]
        apply div_nonneg
        nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          h1, sq_nonneg (x - 1 / 6), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1 / 2),
          mul_nonneg (show 0 ≤ (x : ℝ) by linarith) (show 0 ≤ (y : ℝ) by linarith),
          mul_nonneg (show 0 ≤ (y : ℝ) by linarith) (show 0 ≤ (z : ℝ) by linarith),
          mul_nonneg (show 0 ≤ (z : ℝ) by linarith) (show 0 ≤ (x : ℝ) by linarith)]
        nlinarith
      linarith
    linarith [ht, h2]