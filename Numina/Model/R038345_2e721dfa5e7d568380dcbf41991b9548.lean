import Mathlib

theorem algebra_123917 {b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + b * x + c)
    (h : ∃ x, f x = 0 ∧ x ^ 2 + b * x + c = 2020) :
    ∃! x, f (x - 2020) + f x = 0 := by
  rcases h with ⟨x, hx1, hx2⟩
  have hfx : f x = x ^ 2 + b * x + c := hf x
  rw [hfx] at hx1
  linarith