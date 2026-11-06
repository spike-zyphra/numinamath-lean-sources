import Mathlib

theorem algebra_97874 (x : ℝ) (hx : x > 0) (h : 800 = 8 * 10 ^ 8 * x ^ (-3 / 2 : ℝ)) :
    x ≥ 10 ^ 4 := by
  have h1 : x ^ (-3 / 2 : ℝ) = 1 / 1000000 := by
    have eq1 : x ^ (-3 / 2 : ℝ) = (800) / (8 * 10 ^ 8 : ℝ) := by
      have h_eq : (800 : ℝ) = 8 * 10 ^ 8 * x ^ (-3 / 2 : ℝ) := by linarith
      field_simp at h_eq ⊢
      linarith
    rw [eq1]
    norm_num
  have h2 : x ^ (3 / 2 : ℝ) = 1000000 := by
    have eq1 : x ^ (-3 / 2 : ℝ) = 1 / 1000000 := h1
    have eq2 : x ^ (3 / 2 : ℝ) = (x ^ (-3 / 2 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg]
      norm_num
      all_goals linarith
    rw [eq2, eq1]
    norm_num
  by_contra h4
  push_neg at h4
  have h4' : x < (10 : ℝ) ^ 4 := by linarith
  -- Assume x < 10^4, need to derive contradiction
  have h5 : x ^ (3 / 2 : ℝ) < (10 ^ 4 : ℝ) ^ (3 / 2 : ℝ) := by
    apply Real.rpow_lt_rpow
    linarith
    norm_num
    all_goals linarith
  have h6 : (10 ^ 4 : ℝ) ^ (3 / 2 : ℝ) = 1000000 := by
    have h7 : (10 ^ 4 : ℝ) ^ (3 / 2 : ℝ) = ((10 : ℝ) ^ (4 : ℝ)) ^ (3 / 2 : ℝ) := by norm_num
    rw [h7]
    have h8 : ((10 : ℝ) ^ (4 : ℝ)) ^ (3 / 2 : ℝ) = (10 : ℝ) ^ (4 * (3 / 2 : ℝ)) := by 
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h8]
    norm_num
  have h7 : x ^ (3 / 2 : ℝ) < (1000000 : ℝ) := by
    linarith [h5, h6]
  linarith [h2, h7]