import Mathlib

theorem algebra_141383 (b : ℝ) (h : ∀ x y, 3 * x + (b - 2) * y + 6 > 0 → 3 * x + (b - 2) * y > 0) :
    b = 2 := by 
  have h1 := h 0 0 (by norm_num)
  norm_num at h1
  all_goals try { 
      linarith
    }
  all_goals try { 
      linarith 
    }