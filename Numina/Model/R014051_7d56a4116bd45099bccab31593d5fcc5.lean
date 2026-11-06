import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_125294 (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b > c)
  (h₂ : b + c > a)
  (h₃ : c + a > b) :
  a^2 / (b + c - a) + b^2 / (c + a - b) + c^2 / (a + b - c) ≥ a + b + c := by 
  have ha1 : 0 < a := h₀.1
  have hb1 : 0 < b := h₀.2.1
  have hc1 : 0 < c := h₀.2.2
  have ha2 : b + c - a > 0 := by linarith
  have hb2 : c + a - b > 0 := by linarith
  have hc2 : a + b - c > 0 := by linarith
  have h4 : a ^ 2 / (b + c - a) + b ^ 2 / (c + a - b) + c ^ 2 / (a + b - c) - (a + b + c) ≥ 0 := by
    have pos1 : b + c - a > 0 := by linarith
    have pos2 : c + a - b > 0 := by linarith
    have pos3 : a + b - c > 0 := by linarith
    have h5 : (a ^ 2 / (b + c - a) + b ^ 2 / (c + a - b) + c ^ 2 / (a + b - c) - (a + b + c)) =
              ( (a ^ 2 * (c + a - b) * (a + b - c) +
                  b ^ 2 * (b + c - a) * (a + b - c) +
                  c ^ 2 * (b + c - a) * (c + a - b) - (a + b + c) * (b + c - a) * (c + a - b) * (a + b - c) ) / ( (b + c - a) * (c + a - b) * (a + b - c) ) ) := by
      field_simp [pos1, pos2, pos3]
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha1 hb1, mul_pos ha1 hc1, mul_pos hb1 hc1,
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂),
      mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃),
      mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁)
    ]
    positivity
  linarith