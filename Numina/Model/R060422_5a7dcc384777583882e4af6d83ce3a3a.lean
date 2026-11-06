import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_599455 (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a + b > c)
    (h₂ : b + c > a)
    (h₃ : c + a > b) :
    a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0 := by
  rcases h₀ with ⟨ha_pos, hb_pos, hc_pos⟩
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
            mul_pos ha_pos hb_pos, mul_pos hb_pos hc_pos, mul_pos hc_pos ha_pos,
            mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith),
            mul_pos (show 0 < b + c - a by linarith) (show 0 < c + a - b by linarith),
            mul_pos (show 0 < c + a - b by linarith) (show 0 < a + b - c by linarith)]