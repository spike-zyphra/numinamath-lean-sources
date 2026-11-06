import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_102504 (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b > c) (h₂ : a + c > b) (h₃ : b + c > a) :
  a^2 * c * (a - b) + b^2 * a * (b - c) + c^2 * b * (c - a) ≥ 0 := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have h4 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]