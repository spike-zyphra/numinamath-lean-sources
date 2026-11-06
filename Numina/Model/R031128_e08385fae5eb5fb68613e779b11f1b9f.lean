import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_122238
    (A B C : EuclideanSpace ℝ (Fin 2))
    (a b c : ℝ)
    (h₀ : a = dist B C)
    (h₁ : b = dist A C)
    (h₂ : c = dist A B)
    (h₃ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₄ : a + b > c) (h₅ : a + c > b) (h₆ : b + c > a) :
    a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0 := by
  have ha1 : 0 < a := by linarith
  have hb1 : 0 < b := by linarith
  have hc1 : 0 < c := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
    mul_pos ha1 hb1, mul_pos hb1 hc1, mul_pos ha1 hc1,
    mul_pos (sub_pos.mpr h₄) (sub_pos.mpr h₅),
    mul_pos (sub_pos.mpr h₄) (sub_pos.mpr h₆),
    mul_pos (sub_pos.mpr h₅) (sub_pos.mpr h₆)
  ]