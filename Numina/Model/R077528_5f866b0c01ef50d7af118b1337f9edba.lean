import Mathlib

theorem algebra_196735 (α : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = Real.cos x ^ 2 + Real.cos (x + α) ^ 2 - 2 * Real.cos α * Real.cos x * Real.cos (x + α)) :
    ∃ c, ∀ x, f x = c := by
  use Real.sin α ^ 2 
  intro x 
  have h1 : f x = Real.sin α ^ 2 := by
    rw [h₀ x]
    have h2 : Real.cos (x + α) = Real.cos x * Real.cos α - Real.sin x * Real.sin α := Real.cos_add x α
    rw [h2]
    have h3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    have h4 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    ring_nf 
    <;> simp [Real.sin_sq, Real.cos_sq, h3, h4]
    <;> ring 
  exact h1