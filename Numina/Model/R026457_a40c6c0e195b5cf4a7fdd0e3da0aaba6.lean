import Mathlib

theorem algebra_314208 {t : ℝ} (ht : t ≠ 0) (h : 1/t - abs t = 1) :
    1/t + abs t = Real.sqrt 5 := by
  by_cases h1 : t > 0
  · -- If t > 0, then |t| = t
    have h2 : abs t = t := abs_of_pos h1
    rw [h2] at h
    have h3 : (1 / t) - t = 1 := by
      simpa using h
    have eq1 : t ^ 2 + t - 1 = 0 := by
      field_simp at h3
      nlinarith
    have h4 : t = (-1 + Real.sqrt 5) / 2 := by
      have h5 : t ^ 2 + t - 1 = 0 := eq1
      have h6 : (t - (-1 + Real.sqrt 5) / 2) * (t - (-1 - Real.sqrt 5) / 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > (0 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h6) with ht1 ht2
      · -- t = (-1 + Real.sqrt 5) / 2
        linarith
      · -- t = (-1 - Real.sqrt 5) / 2
        have h7 : t < (0 : ℝ) := by
          nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > (0 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        linarith
    have h5 : abs t = t := abs_of_pos h1
    rw [h5]
    rw [h4]
    have h7 : 1 / ((-1 + Real.sqrt 5) / 2) = (1 + Real.sqrt 5) / 2 := by
      field_simp [(show (-1 + Real.sqrt 5) ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)])]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [h7]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  · -- If t ≤ 0, then t < 0 since t ≠ 0
    have h1 : t < 0 := by
      by_contra h2
      push_neg at h2
      have : t = 0 := by linarith
      contradiction
    have h2 : abs t = -t := abs_of_neg h1
    rw [h2] at h
    have eq1 : (1 / t) + t = 1 := by
      field_simp at h ⊢
      nlinarith
    have eq2 : t ^ 2 - t + 1 = 0 := by
      field_simp at eq1
      nlinarith
    nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (t ^ 2), sq_pos_of_pos (show (0 : ℝ) < 1 by norm_num), sq_nonneg (t + 1 / 2)]