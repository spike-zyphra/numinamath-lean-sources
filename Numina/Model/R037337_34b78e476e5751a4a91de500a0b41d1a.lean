import Mathlib

open Real Set

theorem algebra_8871 :
  IsLeast {x : ℝ | ∃ a b c d : ℝ, x = √(1 + a^2) + √(4 + b^2) + √(9 + c^2) + √(16 + d^2) ∧ a + b + c + d = 10} (10 * √2) := by
  constructor
  · -- Show 10*√2 is in the set
    use 1, 2, 3, 4
    constructor
    · -- Compute the value
      have h1 : √(1 + (1:ℝ)^2) = Real.sqrt 2 := by norm_num
      have h2 : √(4 + (2:ℝ)^2) = Real.sqrt 8 := by norm_num
      have h3 : √(9 + (3:ℝ)^2) = Real.sqrt 18 := by norm_num
      have h4 : √(16 + (4:ℝ)^2) = Real.sqrt 32 := by norm_num
      rw [h1, h2, h3, h4]
      have h5 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h6 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h7 : Real.sqrt 32 = 4 * Real.sqrt 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [h5, h6, h7]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    · -- Check the sum
      norm_num
  · -- Show that 10*√2 is the minimum
    intro x hx
    rcases hx with ⟨a, b, c, d, hx_eq, h_eq⟩
    have h1 : √(1 + a^2) + √(4 + b^2) + √(9 + c^2) + √(16 + d^2) ≥ 10 * Real.sqrt 2 := by
      have h1a : √(1 + a^2) ≥ (1 + a) / Real.sqrt 2 := by
        have h2 : ((1 + a) / Real.sqrt 2) ^ 2 ≤ (1 + a^2 : ℝ) := by
          have h3 : ((1 + a) / Real.sqrt 2) ^ 2 = (1 + a)^2 / (Real.sqrt 2 ^ 2 : ℝ) := by
            ring
          rw [h3]
          have h4 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
          rw [h4]
          nlinarith [sq_nonneg (a - 1 : ℝ)]
        have h5 : ((1 + a) / Real.sqrt 2 : ℝ) ≤ Real.sqrt (1 + a^2 : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          linarith
        linarith
      have h1b : √(4 + b^2) ≥ (2 + b) / Real.sqrt 2 := by
        have h2 : ((2 + b) / Real.sqrt 2) ^ 2 ≤ (4 + b^2 : ℝ) := by
          have h3 : ((2 + b) / Real.sqrt 2) ^ 2 = (2 + b)^2 / (Real.sqrt 2 ^ 2 : ℝ) := by
            ring
          rw [h3]
          have h4 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
          rw [h4]
          nlinarith [sq_nonneg (b - 2 : ℝ)]
        have h5 : ((2 + b) / Real.sqrt 2 : ℝ) ≤ Real.sqrt (4 + b^2 : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          linarith
        linarith
      have h1c : √(9 + c^2) ≥ (3 + c) / Real.sqrt 2 := by
        have h2 : ((3 + c) / Real.sqrt 2) ^ 2 ≤ (9 + c^2 : ℝ) := by
          have h3 : ((3 + c) / Real.sqrt 2) ^ 2 = (3 + c)^2 / (Real.sqrt 2 ^ 2 : ℝ) := by
            ring
          rw [h3]
          have h4 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
          rw [h4]
          nlinarith [sq_nonneg (c - 3 : ℝ)]
        have h5 : ((3 + c) / Real.sqrt 2 : ℝ) ≤ Real.sqrt (9 + c^2 : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          linarith
        linarith
      have h1d : √(16 + d^2) ≥ (4 + d) / Real.sqrt 2 := by
        have h2 : ((4 + d) / Real.sqrt 2) ^ 2 ≤ (16 + d^2 : ℝ) := by
          have h3 : ((4 + d) / Real.sqrt 2) ^ 2 = (4 + d)^2 / (Real.sqrt 2 ^ 2 : ℝ) := by
            ring
          rw [h3]
          have h4 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
          rw [h4]
          nlinarith [sq_nonneg (d - 4 : ℝ)]
        have h5 : ((4 + d) / Real.sqrt 2 : ℝ) ≤ Real.sqrt (16 + d^2 : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          linarith
        linarith
      have h2 : √(1 + a^2) + √(4 + b^2) + √(9 + c^2) + √(16 + d^2) ≥ (1 + a) / Real.sqrt 2 + (2 + b) / Real.sqrt 2 + (3 + c) / Real.sqrt 2 + (4 + d) / Real.sqrt 2 := by
        linarith [h1a, h1b, h1c, h1d]
      have h3 : (1 + a) / Real.sqrt 2 + (2 + b) / Real.sqrt 2 + (3 + c) / Real.sqrt 2 + (4 + d) / Real.sqrt 2 = (10 + (a + b + c + d)) / Real.sqrt 2 := by
        ring
      rw [h3] at h2
      have h4 : (10 + (a + b + c + d)) / Real.sqrt 2 = 10 * Real.sqrt 2 := by
        rw [show a + b + c + d = (10 : ℝ) by linarith [h_eq]]
        have h5 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2)
        field_simp
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2)]
      linarith [h2, h4]
    linarith [h1, hx_eq]