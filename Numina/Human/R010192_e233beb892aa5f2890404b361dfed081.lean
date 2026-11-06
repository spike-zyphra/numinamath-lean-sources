import Mathlib

/- The intersection point of the line $y = 2x + 5$ and the line perpendicular to it that passes through the point $(5, 5)$ is $(1, 7)$ -/
theorem algebra_10750
  (x₀ y₀ m c : ℝ) -- let (x₀, y₀) be the intersection, and let the second line have equation y = mx + c
  (l1 : y₀ = 2 * x₀ + 5) -- (x₀, y₀) lies on line
  (l2 : y₀ = m * x₀ + c) -- (x₀, y₀) lies on line 2
  (perpendicular : m * 2 = -1) -- lines 1 and 2 are perpendicular
  (l2_contains_55 : 5 = m * 5 + c) -- (5, 5) lies on line 2
: x₀ = 1 ∧ y₀ = 7 := by
  rw [show m = -1/2 by linarith] at l2_contains_55 l2
  rw [show c = 15 / 2 by linarith] at l2
  constructor
  linarith
  linarith
