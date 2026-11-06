import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_271862 {a b : ℝ} (f : ℝ → ℝ)
  (hf : f = λ x => (x + a + b) * (x + a - b) * (x - a + b) * (x - a - b)) :
  IsLeast (range f) (-4 * a ^ 2 * b ^ 2) := by 
  constructor
  · -- We will find a specific x such that f(x) = -4 * a^2 * b^2.
    use Real.sqrt (a^2 + b^2)
    rw [hf]
    have h1 : (Real.sqrt (a^2 + b^2)) ^ 2 = a^2 + b^2 := by
      rw [Real.sq_sqrt]
      positivity
    simp [h1]
    nlinarith [Real.sqrt_nonneg (a^2 + b^2), sq_nonneg (Real.sqrt (a^2 + b^2) - a), sq_nonneg (Real.sqrt (a^2 + b^2) + a), sq_nonneg (Real.sqrt (a^2 + b^2) - b), sq_nonneg (Real.sqrt (a^2 + b^2) + b)]
  · -- We need to show that -4 * a^2 * b^2 ≤ f(x) for all x
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    nlinarith [sq_nonneg (x ^ 2 - (a ^ 2 + b ^ 2)), sq_nonneg (x ^ 2 + (a ^ 2 + b ^ 2)), sq_nonneg (x * a - a * x), sq_nonneg (x * b - b * x), sq_nonneg (x), sq_nonneg (a), sq_nonneg (b)]