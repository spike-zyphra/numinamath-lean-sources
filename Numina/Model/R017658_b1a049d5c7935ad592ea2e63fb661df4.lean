import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_115313 (x y z : ℝ) (h₀ : x + y + z = 2) (h₁ : x * y + y * z + z * x = 1) :
    x - y ≤ 2 / sqrt 3 ∧ ∃ x y z, x + y + z = 2 ∧ x * y + y * z + z * x = 1 ∧ x - y = 2 / sqrt 3 := by
  have h2 : z = 2 - x - y := by linarith
  rw [h2] at h₁
  have h3 : x - y ≤ 2 / sqrt 3 := by
    have h4 : (x - y) ^ 2 ≤ (4 / 3) := by
      nlinarith [sq_nonneg (x + y - 2), sq_nonneg (x - y), sq_nonneg ((2 - x - y) - x + y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), sq_nonneg ((2 - x - y) - 2 / 3),
                  Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h5 : (2 / sqrt 3) ^ 2 = (4 / 3 : ℝ) := by
      field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
      <;> norm_num
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h6 : (x - y) ^ 2 ≤ (2 / sqrt 3) ^ 2 := by
      linarith [h4, h5]
    by_cases h7 : x - y ≥ 0
    · -- Assume x - y ≥ 0.
      have h8 : x - y ≤ (2 / sqrt 3) := by
        by_contra h8
        push_neg at h8
        have h9 : (x - y) ^ 2 > (2 / sqrt 3) ^ 2 := by
          have h10 : x - y > (2 / sqrt 3 : ℝ) := by linarith
          have h5' : (2 / sqrt 3 : ℝ) > 0 := by
            positivity
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < 3 by norm_num) (show (0 : ℝ) < 3 by norm_num)]
        nlinarith [h6, h9, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith
    · -- Assume x - y < 0.
      have h8 : x - y < (0 : ℝ) := by linarith
      have h10 : x - y ≤ (2 / sqrt 3) := by
        have h11 : (2 / sqrt 3) > (0 : ℝ) := by
          have h12 : sqrt 3 > 0 := Real.sqrt_pos.mpr (by linarith)
          have h13 : (2 / sqrt 3) > 0 := by positivity
          linarith
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h8, h11]
      linarith
  have h4 : ∃ x y z, x + y + z = 2 ∧ x * y + y * z + z * x = 1 ∧ x - y = 2 / sqrt 3 := by
    use 2 / 3 + Real.sqrt 3 / 3, 2 / 3 - Real.sqrt 3 / 3, 2 / 3
    constructor
    · -- Show that 2/3 + sqrt(3)/3 + 2/3 - sqrt(3)/3 + 2/3 = 2
      field_simp
      <;> ring_nf <;> norm_num
    constructor
    · -- Show that (2/3 + sqrt(3)/3)(2/3 - sqrt(3)/3) + (2/3 - sqrt(3)/3)(2/3) + (2/3)(2/3 + sqrt(3)/3) = 1
      field_simp
      ring_nf
      <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Show that (2/3 + sqrt(3)/3) - (2/3 - sqrt(3)/3) = 2 / sqrt 3
      field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
      <;> ring_nf <;> norm_num
  constructor
  · exact h3
  · exact h4