import Mathlib

/- The curve parameterized by $(x,y) = (2t + 5, 12t^2 - 8t - 7)$ is a parabola, where $t$ is a real number.  Find the equation of the parabola.  Enter the equation in the form "$y = ax^2 + bx + c$". -/
theorem calculus_22030 (x y : ℝ → ℝ) (hx : x = fun t => 2 * t + 5) (hy : y = fun t => 12 * t ^ 2 - 8 * t - 7) : ∀ t, y t = 3 * (x t) ^ 2 + (-34) * (x t) + 88 := by
  intro t
  rw [hy, hx]
  ring