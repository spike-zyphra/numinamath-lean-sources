import Mathlib

theorem algebra_9248 {f : ℝ → ℝ} (g : ℝ → ℝ) (h₀ : ∀ x, g x = f x + f (-x)) :
    ∀ x, g (-x) = g x := by
  intro x
  have h1 : g (-x) = f (-x) + f (-(-x)) := by 
    specialize h₀ (-x)
    simpa using h₀
  have h2 : g x = f x + f (-x) := by 
    specialize h₀ x
    simpa using h₀
  have h3 : f (-(-x)) = f x := by
    simp
  rw [h1, h2, h3]
  ring