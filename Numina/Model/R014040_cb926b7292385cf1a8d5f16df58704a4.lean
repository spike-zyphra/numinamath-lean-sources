import Mathlib

theorem algebra_316654 (f : ℝ → ℝ) (hf : f = fun x => x^3 - Real.sqrt 3 * x^2 - (2 * Real.sqrt 3 + 1) * x + 3 + Real.sqrt 3) :
    ∃ x1 x2 x3, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧ f x1 = 0 ∧ f x2 = 0 ∧ f x3 = 0 ∧
    x1 = 1 + Real.sqrt 3 ∧ x2 = (-1 + Real.sqrt (1 + 4 * Real.sqrt 3)) / 2 ∧ x3 = (-1 - Real.sqrt (1 + 4 * Real.sqrt 3)) / 2 := by
  use 1 + Real.sqrt 3, (-1 + Real.sqrt (1 + 4 * Real.sqrt 3)) / 2, (-1 - Real.sqrt (1 + 4 * Real.sqrt 3)) / 2
  constructor
  · -- Show x1 ≠ x2
    by_contra h
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < 1 + 4 * Real.sqrt 3 by positivity), Real.sq_sqrt (show 0 ≤ (1 + 4 * Real.sqrt 3 : ℝ) by positivity)]
  constructor
  · -- Show x2 ≠ x3
    by_contra h
    have h2 : Real.sqrt (1 + 4 * Real.sqrt 3) = 0 := by nlinarith
    have h4 : Real.sqrt (1 + 4 * Real.sqrt 3) > 0 := by positivity
    nlinarith [Real.sqrt_nonneg (1 + 4 * Real.sqrt 3), Real.sq_sqrt (show 0 ≤ (1 + 4 * Real.sqrt 3 : ℝ) by positivity), h4]
  constructor
  · -- Show x3 ≠ x1
    by_contra h
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < 1 + 4 * Real.sqrt 3 by positivity), Real.sq_sqrt (show 0 ≤ (1 + 4 * Real.sqrt 3 : ℝ) by positivity)]
  constructor
  · -- Show f x1 = 0
    rw [hf]
    have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    have h2 : Real.sqrt 3 ^ 4 = (9 : ℝ) := by
      calc
        Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
        _ = (3) ^ 2 := by rw [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        _ = (9 : ℝ) := by norm_num
    simp [h1, h2]
    <;> nlinarith [sq_nonneg (Real.sqrt 3 ^ 2 - 3), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  constructor
  · -- Show f x2 = 0
    rw [hf]
    have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    have h2 : Real.sqrt (1 + 4 * Real.sqrt 3) ^ 2 = 1 + 4 * Real.sqrt 3 := by
      apply Real.sq_sqrt
      positivity
    have h3 : Real.sqrt (1 + 4 * Real.sqrt 3) ^ 4 = (1 + 4 * Real.sqrt 3) ^ 2 := by
      calc
        Real.sqrt (1 + 4 * Real.sqrt 3) ^ 4 = (Real.sqrt (1 + 4 * Real.sqrt 3) ^ 2) ^ 2 := by ring
        _ = (1 + 4 * Real.sqrt 3) ^ 2 := by rw [Real.sq_sqrt (show 0 ≤ 1 + 4 * Real.sqrt 3 by positivity)]
    simp [h1, h2, h3]
    <;> nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (1 + 4 * Real.sqrt 3), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < 1 + 4 * Real.sqrt 3 by positivity), sq_nonneg (Real.sqrt (1 + 4 * Real.sqrt 3) ^ 2 - (1 + 4 * Real.sqrt 3)), sq_nonneg (Real.sqrt 3 ^ 2 - 3)]
  constructor
  · -- Show f x3 = 0
    rw [hf]
    have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    have h2 : Real.sqrt (1 + 4 * Real.sqrt 3) ^ 2 = 1 + 4 * Real.sqrt 3 := by
      apply Real.sq_sqrt
      positivity
    have h3 : Real.sqrt (1 + 4 * Real.sqrt 3) ^ 4 = (1 + 4 * Real.sqrt 3) ^ 2 := by
      calc
        Real.sqrt (1 + 4 * Real.sqrt 3) ^ 4 = (Real.sqrt (1 + 4 * Real.sqrt 3) ^ 2) ^ 2 := by ring
        _ = (1 + 4 * Real.sqrt 3) ^ 2 := by rw [Real.sq_sqrt (show 0 ≤ 1 + 4 * Real.sqrt 3 by positivity)]
    simp [h1, h2, h3]
    <;> nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (1 + 4 * Real.sqrt 3), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < 1 + 4 * Real.sqrt 3 by positivity), sq_nonneg (Real.sqrt (1 + 4 * Real.sqrt 3) ^ 2 - (1 + 4 * Real.sqrt 3)), sq_nonneg (Real.sqrt 3 ^ 2 - 3)]
  constructor
  · -- Show x1 = 1 + Real.sqrt 3
    rfl
  constructor
  · -- Show x2 = (-1 + Real.sqrt (1 + 4 * Real.sqrt 3)) / 2
    rfl
  · -- Show x3 = (-1 - Real.sqrt (1 + 4 * Real.sqrt 3)) / 2
    rfl