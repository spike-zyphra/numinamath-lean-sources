import Mathlib

theorem algebra_299519 (a b : ℝ) (h : a^2 + a * b + b^2 = 1) (t : ℝ) (ht : t = a * b - a^2 - b^2) :
    t ∈ Set.Icc (-3) (-1 / 3) := by
  have ht' : t = 2 * (a * b) - 1 := by
    rw [ht]
    nlinarith

  have h1 : -1 ≤ a * b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

  have h2 : a * b ≤ 1 / 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  
  rw [ht']
  constructor
  · -- Show that $t \geq -3$ (lower bound)
    nlinarith
  · -- Show that $t \leq -\frac{1}{3}$ (upper bound)
    nlinarith