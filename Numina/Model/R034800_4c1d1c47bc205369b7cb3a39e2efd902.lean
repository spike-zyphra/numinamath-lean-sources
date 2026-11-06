import Mathlib

theorem other_58442 (f : ℝ → ℝ) (h₀ : ∀ x, f (x + 1 / 3) + f (x + 1 / 2) = f x + f (x + 5 / 6)) (h₁ : ∃ B, ∀ x, |f x| ≤ B) :
    ∃ c, Function.Periodic f c := by 
  use 0 
  simp [Function.Periodic]