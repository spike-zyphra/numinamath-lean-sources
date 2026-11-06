import Mathlib

theorem algebra_195223 (a : ℝ) (h : ∃ d, ∀ n, 1 + d * n = 6 + 2 * a * n) :
    a = 1 := by
  rcases h with ⟨d, hd⟩
  have h0 := hd 0
  norm_num at h0 
  all_goals linarith