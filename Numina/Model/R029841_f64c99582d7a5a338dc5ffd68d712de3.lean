import Mathlib

theorem algebra_304568 {a k : ℝ} (ha : a ≠ 0) (h : √2 = k * a - 2) (h' : √2 = (Real.sqrt 2 - 1) * a) :
    k = 1 := by
  have eq1 : a = Real.sqrt 2 / (Real.sqrt 2 - 1) := by
    have h2 : Real.sqrt 2 - 1 ≠ 0 := by
      have h1 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h3 : (Real.sqrt 2 : ℝ) - 1 > 0 := by linarith
      linarith
    have h4 : a = Real.sqrt 2 / (Real.sqrt 2 - 1) := by 
      field_simp [h2] at h' ⊢
      linarith
    exact h4

  have eq2 : k = 1 := by
    rw [eq1] at h 
    have h2 : Real.sqrt 2 - 1 ≠ 0 := by
      have h1 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h3 : (Real.sqrt 2 : ℝ) - 1 > 0 := by linarith
      linarith
    field_simp [h2] at h ⊢
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (k - 1)]
  exact eq2