import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_3735 (a b c : ℝ) (h_pos : 0 < a ∧ 0 < b ∧ 0 < c)
  (h_sides : a < b + c ∧ b < a + c ∧ c < a + b) :
  (a + b + c)^2 < 4 * (a * b + a * c + b * c) := by
    have h₁ : a < b + c := h_sides.1
    have h₂ : b < a + c := h_sides.2.1
    have h₃ : c < a + b := h_sides.2.2
    nlinarith [sq_pos_of_pos h_pos.1, sq_pos_of_pos h_pos.2.1, sq_pos_of_pos h_pos.2.2,
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      h₁, h₂, h₃, mul_pos h_pos.1 h_pos.2.1, mul_pos h_pos.1 h_pos.2.2, mul_pos h_pos.2.1 h_pos.2.2]