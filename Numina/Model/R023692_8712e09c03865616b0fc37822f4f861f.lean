import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_279493 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^2 + y^2 + z^2 = 1 ∧ t = x * y / z + y * z / x + z * x / y} (Real.sqrt 3) := by
  constructor
  · -- Show that `√3` is in the set
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3
    constructor
    · -- Show `√3` is positive
      have h1 : 0 < Real.sqrt 3 / 3 := by
        have h2 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
        linarith
      linarith
    constructor
    · -- Show `√3` is positive
      have h1 : 0 < Real.sqrt 3 / 3 := by
        have h2 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
        linarith
      linarith
    constructor
    · -- Show `√3` is positive
      have h1 : 0 < Real.sqrt 3 / 3 := by
        have h2 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
        linarith
      linarith
    constructor
    · -- Verify `(√3/3)² + (√3/3)² + (√3/3)² = 1`
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)
      nlinarith
    · -- Verify `√3 = (√3/3 * √3/3) / (√3/3) + (√3/3 * √3/3) / (√3/3) + (√3/3 * √3/3) / (√3/3)`
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), h1, Real.sqrt_nonneg 3]
  · -- Show that `√3` is the least element in the set
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, heq⟩
    -- We need to show t ≥ √3
    have h4 : (x * y / z + y * z / x + z * x / y) ≥ Real.sqrt 3 := by
      have h7 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := by
        have h8 : (x * y / z + y * z / x + z * x / y) ^ 2 = (x * y / z) ^ 2 + (y * z / x) ^ 2 + (z * x / y) ^ 2 + 2 * (x * y / z * (y * z / x) + x * y / z * (z * x / y) + y * z / x * (z * x / y)) := by
          ring
        have h9 : x * y / z * (y * z / x) = y ^ 2 := by
          field_simp
          <;> nlinarith
        have h10 : x * y / z * (z * x / y) = x ^ 2 := by
          field_simp
          <;> nlinarith
        have h11 : y * z / x * (z * x / y) = z ^ 2 := by
          field_simp
          <;> nlinarith
        rw [h8, h9, h10, h11]
        nlinarith [sq_nonneg (x * y / z - y * z / x), sq_nonneg (y * z / x - z * x / y), sq_nonneg (z * x / y - x * y / z), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
      have h6 : (x * y / z + y * z / x + z * x / y) ≥ 0 := by
        positivity
      have h7' : (x * y / z + y * z / x + z * x / y) ≥ Real.sqrt 3 := by
        have h8' : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := h7
        have h8' : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := h7
        have h6' : (x * y / z + y * z / x + z * x / y) ≥ 0 := by positivity
        have h8' : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := h7
        have h9 : Real.sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) ≥ Real.sqrt (3) := Real.sqrt_le_sqrt (by nlinarith)
        have h11 : Real.sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) = (x * y / z + y * z / x + z * x / y) := by
          rw [Real.sqrt_sq_eq_abs]
          rw [abs_of_nonneg (by positivity)]
        linarith
      linarith
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]