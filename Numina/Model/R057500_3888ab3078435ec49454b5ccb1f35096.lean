import Mathlib

theorem algebra_11649 {a b : ℝ} (ha : a > 0) (hb : b > 0)
    (h : a^2 * 3 = b^2 * 9) (h' : ∃ x y, x^2 / 9 - y^2 / 3 = 1 ∧ y = 2 ∧ x = Real.sqrt 3) :
    a^2 = 3 ∧ b^2 = 9 := by
  rcases h' with ⟨x, y, h1, h2, h3⟩
  rw [h2, h3] at h1
  have h4 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  rw [h4] at h1
  norm_num at h1
  all_goals try { nlinarith }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    linarith 
  }
  all_goals try { 
    nlinarith 
  }