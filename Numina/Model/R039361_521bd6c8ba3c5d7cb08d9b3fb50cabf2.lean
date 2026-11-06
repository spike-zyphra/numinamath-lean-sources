import Mathlib

theorem algebra_244006 (f : ℝ → ℝ) (hf : ∀ x, f (2 * x / (3 * x ^ 2 + 1)) = x ^ 2)
    (a : ℝ) (ha : 0 < a) (h : ∀ x ∈ Set.Icc (1 / 4) a, f (2 * x / (3 * x ^ 2 + 1)) = x ^ 2) :
    a = 4 / 3 := by
  have h1 := hf (1 / 4)
  have h2 := hf (4 / 3)
  norm_num at h1 h2
  all_goals linarith