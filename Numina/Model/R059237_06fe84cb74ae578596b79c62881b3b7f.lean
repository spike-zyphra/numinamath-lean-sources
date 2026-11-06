import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_599723
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b > c)
  (h₂ : b + c > a)
  (h₃ : c + a > b) :
  a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by

  have h4 : 0 < a := h₀.1
  have h5 : 0 < b := h₀.2.1
  have h6 : 0 < c := h₀.2.2
  -- Solve by using nonlinear arithmetic solver in Lean, which can solve nonlinear polynomial.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
          mul_pos h4 h5, mul_pos h4 h6, mul_pos h5 h6,
          mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith),
          mul_pos (show 0 < b + c - a by linarith) (show 0 < c + a - b by linarith),
          mul_pos (show 0 < c + a - b by linarith) (show 0 < a + b - c by linarith)]