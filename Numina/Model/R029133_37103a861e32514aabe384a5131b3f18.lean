import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_153399 {f : ℝ → ℝ} (hf : f = λ x => x^3 + x) :
    Odd f ∧ Monotone f := by 
  constructor
  · -- Show that f is odd
    rw [hf]
    use λ x => (x^3 + x - 1) / 2 
    funext x 
    simp 
    <;> ring 
  · -- Show that f is monotone 
    rw [hf]
    intro x y hxy
    simp at *
    have h1 : y ≥ x := by linarith
    have h2 : y^3 + y - (x^3 + x) ≥ 0 := by 
      have h3 : y ≥ x := h1 
      have h4 : y^3 + y - (x^3 + x) = (y - x) * (y^2 + y * x + x^2 + 1) := by 
        ring 
      rw [h4] 
      have h5 : y - x ≥ 0 := by linarith 
      have h6 : y^2 + y * x + x^2 + 1 ≥ 0 := by 
        nlinarith [sq_nonneg (y + x), sq_nonneg (y - x), sq_nonneg (y), sq_nonneg (x)]
      nlinarith 
    linarith