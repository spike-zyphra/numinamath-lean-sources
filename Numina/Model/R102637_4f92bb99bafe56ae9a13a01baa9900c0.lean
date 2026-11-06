import Mathlib

theorem algebra_7955 {a b : ℝ} (h : (a + 3)^2 = -abs (b - 1)) :
    a = -3 ∧ b = 1 := by 
  have h1 : (a + 3) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h2 : abs (b - 1) ≥ 0 := by 
    apply abs_nonneg
  have h3 : (a + 3) ^ 2 = 0 := by 
    linarith [h, h1, h2] 
  have ha : a = -3 := by 
    have h4 : a + 3 = 0 := by 
      rw [sq_eq_zero_iff] at h3 
      exact h3 
    linarith 
  have hb : b = 1 := by 
    have h4 : abs (b - 1) = 0 := by 
      linarith [h, h3] 
    have h5 : b - 1 = 0 := by 
      rwa [abs_eq_zero] at h4 
    linarith 
  exact ⟨ha, hb⟩