import Mathlib

theorem algebra_272314 (v : ℕ → ℝ) (h : ∀ n, v n > 0)
    (h1 : v 1 = 2) (h2 : ∀ n, v (n + 1) = 2 / n) :
    ∀ n, v n = 2 * (n - 1) := by 
  intro n
  -- The inconsistency comes from applying h2 with n = 0
  have h3 := h2 0
  norm_num at h3 
  all_goals 
    linarith [h1, h3, h 1]