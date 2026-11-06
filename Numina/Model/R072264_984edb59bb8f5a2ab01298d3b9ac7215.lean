import Mathlib

theorem algebra_7961 {P Q : ℝ → ℝ → ℝ}
    (hP : P = fun a b => a^2 + 3 * a * b + b^2)
    (hQ : Q = fun a b => a^2 - 3 * a * b + b^2) :
    ∀ a b, P a b - (Q a b - 2 * P a b - (-P a b - Q a b)) = 12 * a * b := by
  intro a b
  simp only [hP, hQ]
  ring