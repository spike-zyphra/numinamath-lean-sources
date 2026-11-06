import Mathlib

theorem algebra_256031 {x y : ℝ} (hx : x = Real.logb 10 2) (hy : y = Real.logb 10 5)
    (hxy : x * y = 0.210) : x = 0.3 ∧ y = 0.7 := by
  have h1 : x + y = 1 := by
    rw [hx, hy]
    have h : Real.logb 10 2 + Real.logb 10 5 = 1 := by 
      have h2 : Real.logb 10 2 + Real.logb 10 5 = Real.logb 10 (2 * 5) := by 
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      have h3 : Real.logb 10 (2 * 5) = 1 := by 
        norm_num [Real.logb_eq_iff_rpow_eq]
      linarith [h2, h3]
    linarith
  have h2 : y = 1 - x := by linarith 
  rw [h2] at hxy 
  have heq : x * (1 - x) = (0.210 : ℝ) := by
    simpa using hxy 
  have h3 : x ^ 2 - x + (0.210 : ℝ) = (0 : ℝ) := by
    nlinarith 
  have h4 : (x - (0.3 : ℝ)) * (x - (0.7 : ℝ)) = 0 := by 
    ring_nf at h3 ⊢ 
    nlinarith 
  cases' (mul_eq_zero.1 h4) with h5 h6 
  · -- Case x - 0.3 = 0
    have hx1 : x = (0.3 : ℝ) := by linarith 
    have hy1 : y = (0.7 : ℝ) := by 
      linarith [h1, hx1]
    exact ⟨hx1, hy1⟩
  · -- Case x - 0.7 = 0 
    have hx2 : x = (0.7 : ℝ) := by linarith
    have h7 : y = (0.3 : ℝ) := by 
      linarith [h1, hx2]
    have h8 : x < y := by 
      rw [hx, hy] 
      have h25 : (2 : ℝ) < (5 : ℝ) := by norm_num 
      have h256 : Real.logb 10 (2 : ℝ) < Real.logb 10 (5 : ℝ) := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
      nlinarith [h256] 
    nlinarith [show x < y from by nlinarith [h8], h7, hx2]