import Mathlib

theorem algebra_169882 (a : ℕ → ℝ) (x0 : ℝ)
    (h1 : x0^4 + a 1 * x0^3 + a 2 * x0^2 + a 3 * x0 + a 4 = 0)
    (h2 : 4 * x0^3 + 3 * a 1 * x0^2 + 2 * a 2 * x0 + a 3 = 0) :
    (X - x0)^2 ∣ X^4 + a 1 * X^3 + a 2 * X^2 + a 3 * X + a 4 := by 
  have eq3 : X^4 + a 1 * X^3 + a 2 * X^2 + a 3 * X + a 4 = 
    (X - x0) ^ 2 * (X^2 + (a 1 + 2 * x0) * X + (a 2 + 2 * x0 * (a 1 + 2 * x0) - x0^2)) := by
    ring_nf
    have eq1 : a 4 = -x0^4 - a 1 * x0^3 - a 2 * x0^2 - a 3 * x0 := by
      linarith
    have eq2 : a 3 = -4 * x0^3 - 3 * a 1 * x0^2 - 2 * a 2 * x0 := by
      linarith
    rw [eq1, eq2]
    ring_nf
  rw [eq3]
  all_goals simp