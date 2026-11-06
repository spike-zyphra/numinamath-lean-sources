import Mathlib

theorem algebra_220096 (f : ℝ → ℝ) (hf : f = fun x => x^3 - x - 2 / (3 * Real.sqrt 3)) :
    ∃ x1 x2 x3 : ℝ, x1 = 2 / Real.sqrt 3 ∧ x2 = -1 / Real.sqrt 3 ∧ x3 = -1 / Real.sqrt 3 ∧
    f x1 = 0 ∧ f x2 = 0 ∧ f x3 = 0 := by
  use 2 / Real.sqrt 3, -1 / Real.sqrt 3, -1 / Real.sqrt 3
  constructor
  · -- The first root is as claimed.
    rfl
  constructor
  · -- The second root is as claimed.
    rfl
  constructor
  · -- The third root is as claimed.
    rfl
  constructor
  · -- Show that f(2/√3) = 0
    rw [hf]
    have h1 : Real.sqrt 3 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    field_simp
    nlinarith [Real.sqrt_nonneg 3, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
              sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (2 - Real.sqrt 3), sq_nonneg (2 + Real.sqrt 3),
              Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  constructor
  · -- Show that f(-1/√3) = 0
    rw [hf]
    have h1 : Real.sqrt 3 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    field_simp
    nlinarith [Real.sqrt_nonneg 3, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
              sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 3 - 1), sq_nonneg (Real.sqrt 3 + 1),
              Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  · -- Show that f(-1/√3) = 0
    rw [hf]
    have h1 : Real.sqrt 3 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    field_simp
    nlinarith [Real.sqrt_nonneg 3, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
              sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 3 - 1), sq_nonneg (Real.sqrt 3 + 1),
              Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]