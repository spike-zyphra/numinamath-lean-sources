import Mathlib

open Real

theorem other_42290 (p : ℕ → ℝ) (hp0 : p 0 = 1) (hp1 : p 1 = 0) (hp2 : p 2 = 1 / 2) (hp : ∀ n, p (n + 1) = p n / (n + 1)) :
    p 50 = 1 / 99 := by
  have h1 := hp 0
  norm_num [hp0] at h1
  all_goals linarith [hp1, h1]