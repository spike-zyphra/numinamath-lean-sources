import Mathlib

theorem algebra_599944 (p : ℤ → ℝ)
    (h₀ : ∀ x, p x = (1 / 630) * x ^ 9 - (1 / 21) * x ^ 7 + (13 / 20) * x ^ 5 - (82 / 63) * x ^ 3 + (32 / 35) * x) :
    ∀ x, ∃ n, p x = n := by
  intro x 
  refine' ⟨p x, by simp [h₀]⟩