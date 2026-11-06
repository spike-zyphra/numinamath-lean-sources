import Mathlib

open Real

theorem algebra_609676 (f : ℕ → ℝ) (hf : f 0 = 1) (hf' : f 1 = 10^8)
    (h : ∀ n, f (n + 1) = (f n + f (n + 1)) / 2 ∧ f (n + 2) = 2 / (1 / f n + 1 / f (n + 1))) :
    IsLeast {x | ∃ a b, x = min a b ∧ a = f 2017 ∧ b = f 2018} 10000 := by
  -- Contradiction with initial conditions
  have h1 := h 0
  have h11 := h1.1
  rw [hf] at h11
  rw [hf'] at h11
  norm_num at h11
  all_goals
    norm_num [IsLeast, lowerBounds] at *
    <;> try { linarith }
    <;> try { tauto }