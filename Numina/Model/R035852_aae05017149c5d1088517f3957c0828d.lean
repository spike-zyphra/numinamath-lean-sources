import Mathlib

theorem algebra_13801 : IsGreatest {x : ℝ | 2*x^2 + 6*x + 9 = 7*x*Real.sqrt (2*x + 3)} (9 + 6*Real.sqrt 3) := by
  constructor
  · -- Show that 9 + 6*sqrt(3) is in the set
    have h1 : Real.sqrt 3 ≥ 0 := by positivity
    have h2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have h3 : 2 * (9 + 6 * Real.sqrt 3) + 3 = (3 + 2 * Real.sqrt 3) ^ 2 := by
      nlinarith [h2, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
    have h4 : Real.sqrt (2 * (9 + 6 * Real.sqrt 3) + 3) = (3 + 2 * Real.sqrt 3) := by
      rw [h3]
      have h5 : 0 ≤ (3 + 2 * Real.sqrt 3 : ℝ) := by nlinarith [show Real.sqrt 3 ≥ 0 by positivity]
      rw [Real.sqrt_sq (h5)]
    have h5 : 2 * (9 + 6 * Real.sqrt 3) ^ 2 + 6 * (9 + 6 * Real.sqrt 3) + 9 = 7 * (9 + 6 * Real.sqrt 3) * Real.sqrt (2 * (9 + 6 * Real.sqrt 3) + 3) := by
      rw [h4]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), h2, sq_nonneg (Real.sqrt 3)]
    exact h5
  · -- Show that 9 + 6*sqrt(3) is the greatest element in the set
    intro x hx
    rw [Set.mem_setOf] at hx
    by_contra h
    push_neg at h
    have h1 : 2 * x + 3 ≥ 0 := by
      by_contra h2
      push_neg at h2
      have h3 : Real.sqrt (2 * x + 3) = 0 := by
        rw [Real.sqrt_eq_zero']
        all_goals nlinarith
      have h4 : 7 * x * Real.sqrt (2 * x + 3) = 0 := by
        rw [h3]
        norm_num
      nlinarith
    have h2 : Real.sqrt (2 * x + 3) ≥ 0 := by positivity
    have h3 : (Real.sqrt (2 * x + 3)) ^ 2 = 2 * x + 3 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h4 : x > 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), h, Real.sqrt_nonneg (2 * x + 3), Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x + 3 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    nlinarith [sq_nonneg (Real.sqrt (2 * x + 3) - (3 + 2 * Real.sqrt 3)), sq_nonneg (x - (9 + 6 * Real.sqrt 3)), Real.sqrt_nonneg (2 * x + 3), Real.sqrt_nonneg (3), sq_nonneg (x - (9 + 6 * Real.sqrt 3)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x + 3 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]