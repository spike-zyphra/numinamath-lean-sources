import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_597811 (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b > c)
  (h₂ : b + c > a)
  (h₃ : c + a > b) :
  1 ≤ a / (3 * a - b + c) + b / (3 * b - c + a) + c / (3 * c - a + b) := by
  have h4 : 3 * a - b + c > 0 := by 
    nlinarith
  have h5 : 3 * b - c + a > 0 := by 
    nlinarith
  have h6 : 3 * c - a + b > 0 := by 
    nlinarith
  have h7 : a / (3 * a - b + c) + b / (3 * b - c + a) + c / (3 * c - a + b) - 1 ≥ 0 := by 
    have h8 : (3 * a - b + c) > 0 := h4
    have h9 : (3 * b - c + a) > 0 := h5
    have h10 : (3 * c - a + b) > 0 := h6
    have h11 : a / (3 * a - b + c) + b / (3 * b - c + a) + c / (3 * c - a + b) - 1 =
        ( a * ( (3 * b - c + a) * (3 * c - a + b) ) + b * ( (3 * a - b + c) * (3 * c - a + b) ) + c * ( (3 * a - b + c) * (3 * b - c + a) ) - ( (3 * a - b + c) * (3 * b - c + a) * (3 * c - a + b) ) ) / ( (3 * a - b + c) * (3 * b - c + a) * (3 * c - a + b) ) := by 
      field_simp
      ring
    rw [h11]
    apply div_nonneg
    nlinarith [ sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
               sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b), 
               mul_pos h₀.1 h₀.2.1, mul_pos h₀.2.1 h₀.2.2, mul_pos h₀.1 h₀.2.2, 
               mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), 
               mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃), 
               mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁) ]
    all_goals
      positivity
  linarith