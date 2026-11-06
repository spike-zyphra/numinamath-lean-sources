import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_599085
    (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : c < a + b)
    (h₂ : b < a + c)
    (h₃ : a < b + c)
    (h₄ : a + b + c = 1) :
    a^2 + b^2 + c^2 + 4 * a * b * c ≤ 1 / 2 := by
        have h5 : a > 0 := h₀.left
        have h6 : b > 0 := h₀.right.left
        have h7 : c > 0 := h₀.right.right
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos h5 h6, mul_pos h5 h7, mul_pos h6 h7,
          mul_pos (show 0 < a + b - c by nlinarith) (show 0 < a + c - b by nlinarith),
          mul_pos (show 0 < a + c - b by nlinarith) (show 0 < b + c - a by nlinarith),
          mul_pos (show 0 < a + b - c by nlinarith) (show 0 < b + c - a by nlinarith)
         ]