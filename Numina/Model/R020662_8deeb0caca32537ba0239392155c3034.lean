import Mathlib

open Real Set

theorem inequalities_133046 (a : ℝ) (h : a < 9 * a^3 - 11 * a ∧ 9 * a^3 - 11 * a < abs a) :
    a ∈ Ioo (-2 * sqrt 3 / 3) (-sqrt 10 / 3) := by
  rcases h with ⟨h1, h2⟩
  by_cases h3 : a < 0
  · -- Assume a < 0, so |a| = -a
    have h4 : abs a = -a := by
      rw [abs_of_neg h3]
    rw [h4] at h2
    have h2' : 9 * a^3 - 10 * a < 0 := by nlinarith
    have h3' : a < 0 := h3
    have h5 : a^2 > (10 / 9 : ℝ) := by
      nlinarith [sq_nonneg (a^2), sq_pos_of_neg h3', sq_nonneg (a ^ 2 - 10 / 9), sq_nonneg (a - 0)]
    have h10 : a < -(sqrt 10 / 3) := by
      nlinarith [Real.sqrt_nonneg 10, Real.sqrt_pos.mpr (show (10 : ℝ) > 0 by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), 
        sq_nonneg (a + (sqrt 10 / 3)), Real.sqrt_nonneg 10]
    have h6 : 9 * a^3 - 12 * a > 0 := by nlinarith
    have h7 : a^2 < (4 / 3 : ℝ) := by
      nlinarith [sq_nonneg (a^2), sq_pos_of_neg h3', sq_nonneg (a ^ 2 - 4 / 3), sq_nonneg (a - 0)]
    have h11 : -2 * sqrt 3 / 3 < a := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        sq_nonneg (a - (-2 * sqrt 3 / 3)), Real.sqrt_nonneg 3]
    constructor <;> nlinarith [h11, h10]
  · -- Assume a ≥ 0, so |a| = a
    have h3' : a ≥ 0 := by linarith
    have h4 : abs a = a := by
      rw [abs_of_nonneg (show 0 ≤ a by linarith)]
    rw [h4] at h2
    have h2' : 9 * a^3 - 12 * a < 0 := by nlinarith
    nlinarith [sq_nonneg (a^2 - 4 / 3), sq_nonneg (a - 2 * sqrt 3 / 3), Real.sqrt_nonneg 3, 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (a), sq_nonneg (a ^ 2 - 4 / 3)]