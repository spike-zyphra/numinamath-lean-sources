import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_249024 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  3 ≤ a / (b + c - a) + b / (c + a - b) + c / (a + b - c) := by
  have h1 : 0 < b + c - a := by linarith
  have h2 : 0 < c + a - b := by linarith
  have h3 : 0 < a + b - c := by linarith
  have h4 : a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3 ≥ 0 := by
    have h4' : a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3 =
        (a * (c + a - b) * (a + b - c) + b * (b + c - a) * (a + b - c) + c * (b + c - a) * (c + a - b) - 3 * (b + c - a) * (c + a - b) * (a + b - c)) / ((b + c - a) * (c + a - b) * (a + b - c)) := by
      field_simp
      ring
    rw [h4'] at *
    have h5 : 0 < (b + c - a) * (c + a - b) * (a + b - c) := by
      positivity
    have h6 : a * (c + a - b) * (a + b - c) + b * (b + c - a) * (a + b - c) + c * (b + c - a) * (c + a - b) - 3 * (b + c - a) * (c + a - b) * (a + b - c) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3,
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith),
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)]
    apply div_nonneg
    linarith
    all_goals linarith
  linarith