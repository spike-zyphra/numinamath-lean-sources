import Mathlib

theorem algebra_94312 (x : ℝ) (h : ∃ r, ∀ n, (n * x + n) = r ^ n) :
    4 * x + 4 = -13.5 := by

  rcases h with ⟨r, hr⟩
  have h0 := hr 0
  norm_num at h0
  all_goals linarith