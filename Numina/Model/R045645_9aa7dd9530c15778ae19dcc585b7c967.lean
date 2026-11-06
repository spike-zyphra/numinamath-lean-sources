import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_223892 :
  IsLeast {a : ℝ | ∃ x y z : ℝ, x ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧
    a = (sqrt (3 * x^4 + y) + sqrt (3 * y^4 + z) + sqrt (3 * z^4 + x) - 3) /
    (x * y + y * z + z * x)} 1 := by 
  constructor
  · -- Show 1 is in the set
    use 1, 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    have h1 : sqrt (3 * (1: ℝ)^4 + (1: ℝ)) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    norm_num
  · -- Show it's the minimum
    intro a
    rintro ⟨x, y, z, hx, hy, hz, ha⟩
    have h1 : sqrt (3 * x^4 + y) ≥ x^2 + 1 := by
      have h2 : (sqrt (3 * x^4 + y)) ^ 2 ≥ (x^2 + 1) ^ 2 := by
        have h3 : (sqrt (3 * x^4 + y)) ^ 2 = 3 * x^4 + y := by
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg (x^2), sq_nonneg (y - 1), hz]
        have h4 : (x^2 + 1) ^ 2 = x^4 + 2 * x^2 + 1 := by
          nlinarith [sq_nonneg (x^2)]
        have h5 : 3 * x^4 + y ≥ x^4 + 2 * x^2 + 1 := by
          nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (y - x^2), mul_nonneg (show 0 ≤ x - 1 by nlinarith) (show 0 ≤ y - 1 by nlinarith)]
        rw [h3, h4]
        nlinarith
      have h5 : sqrt (3 * x^4 + y) ≥ x^2 + 1 := by
        nlinarith [Real.sqrt_nonneg (3 * x^4 + y), Real.sqrt_nonneg (3 * x^4 + y), sq_nonneg (x^2), sq_nonneg (x^2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 3 * x^4 + y by positivity)]
      exact h5
    have h2 : sqrt (3 * y^4 + z) ≥ y^2 + 1 := by
      have h2 : (sqrt (3 * y^4 + z)) ^ 2 ≥ (y^2 + 1) ^ 2 := by
        have h3 : (sqrt (3 * y^4 + z)) ^ 2 = 3 * y^4 + z := by
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg (y^2), sq_nonneg (z - 1), hz]
        have h4 : (y^2 + 1) ^ 2 = y^4 + 2 * y^2 + 1 := by
          nlinarith [sq_nonneg (y^2)]
        have h5 : 3 * y^4 + z ≥ y^4 + 2 * y^2 + 1 := by
          nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (z - y^2), mul_nonneg (show 0 ≤ y - 1 by nlinarith) (show 0 ≤ z - 1 by nlinarith)]
        rw [h3, h4]
        nlinarith
      have h5 : sqrt (3 * y^4 + z) ≥ y^2 + 1 := by
        nlinarith [Real.sqrt_nonneg (3 * y^4 + z), Real.sqrt_nonneg (3 * y^4 + z), sq_nonneg (y^2), sq_nonneg (y^2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 3 * y^4 + z by positivity)]
      exact h5
    have h3 : sqrt (3 * z^4 + x) ≥ z^2 + 1 := by
      have h2 : (sqrt (3 * z^4 + x)) ^ 2 ≥ (z^2 + 1) ^ 2 := by
        have h3 : (sqrt (3 * z^4 + x)) ^ 2 = 3 * z^4 + x := by
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg (z^2), sq_nonneg (x - 1), hz]
        have h4 : (z^2 + 1) ^ 2 = z^4 + 2 * z^2 + 1 := by
          nlinarith [sq_nonneg (z^2)]
        have h5 : 3 * z^4 + x ≥ z^4 + 2 * z^2 + 1 := by
          nlinarith [sq_nonneg (z - 1), sq_nonneg (x - 1), sq_nonneg (x - z^2), mul_nonneg (show 0 ≤ z - 1 by nlinarith) (show 0 ≤ x - 1 by nlinarith)]
        rw [h3, h4]
        nlinarith
      have h5 : sqrt (3 * z^4 + x) ≥ z^2 + 1 := by
        nlinarith [Real.sqrt_nonneg (3 * z^4 + x), Real.sqrt_nonneg (3 * z^4 + x), sq_nonneg (z^2), sq_nonneg (z^2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 3 * z^4 + x by positivity)]
      exact h5
    have h7 : sqrt (3 * x^4 + y) + sqrt (3 * y^4 + z) + sqrt (3 * z^4 + x) - 3 ≥ x^2 + y^2 + z^2 := by
      nlinarith [h1, h2, h3, sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have h9 : x^2 + y^2 + z^2 ≥ x * y + y * z + z * x := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have h10 : sqrt (3 * x^4 + y) + sqrt (3 * y^4 + z) + sqrt (3 * z^4 + x) - 3 ≥ x * y + y * z + z * x := by
      nlinarith [h7, h9, sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have h11 : (sqrt (3 * x^4 + y) + sqrt (3 * y^4 + z) + sqrt (3 * z^4 + x) - 3) / (x * y + y * z + z * x) ≥ 1 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [h10, sq_nonneg (x * y + y * z + z * x), hz]
    linarith [h11, ha]