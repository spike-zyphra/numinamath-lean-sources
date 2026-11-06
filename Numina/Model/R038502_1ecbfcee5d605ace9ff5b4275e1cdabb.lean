import Mathlib

theorem algebra_10237 {a : ℕ → ℝ} (ha : a 1 = 2) (ha' : a 2 = 5)
  (h : ∀ n, a (n + 1) * a n = a n * a (n - 1)) : a 12 = 5 := by

  have ha0 : a 0 = 5 := by 
    have h10 := h 1
    simp [ha, ha'] at h10 
    nlinarith

  have h00 := h 0 
  simp [ha] at h00
  rw [ha0] at h00 
  norm_num at h00
  all_goals linarith