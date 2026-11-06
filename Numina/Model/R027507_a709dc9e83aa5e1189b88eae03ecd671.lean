import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_220734 (a b c : ℝ)
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (h : a + b > c)
  (h' : b + c > a)
  (h'' : c + a > b) :
  3 < (a^2 + 2 * b * c) / (b^2 + c^2) + (b^2 + 2 * c * a) / (c^2 + a^2) +
    (c^2 + 2 * a * b) / (a^2 + b^2) := by
  have h₁ : 0 < b^2 + c^2 := by nlinarith
  have h₂ : 0 < c^2 + a^2 := by nlinarith
  have h₃ : 0 < a^2 + b^2 := by nlinarith

  have h4 : (a^2 + 2 * b * c) / (b^2 + c^2) + (b^2 + 2 * c * a) / (c^2 + a^2) + (c^2 + 2 * a * b) / (a^2 + b^2) - 3 > 0 := by

    have pos1 : 0 < (b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2) := by positivity

    have eq1 : (a^2 + 2 * b * c) / (b^2 + c^2) + (b^2 + 2 * c * a) / (c^2 + a^2) + (c^2 + 2 * a * b) / (a^2 + b^2) - 3 =
        ((a^2 + 2 * b * c) * (c^2 + a^2) * (a^2 + b^2) + (b^2 + 2 * c * a) * (b^2 + c^2) * (a^2 + b^2) + (c^2 + 2 * a * b) * (b^2 + c^2) * (c^2 + a^2) - 3 * (b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2)) / ((b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2)) := by 
      field_simp 
      <;> ring
  
    rw [eq1] at *
    apply div_pos
    · -- Show that the numerator is positive 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
                sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos ha (show (0 : ℝ) < b * c by nlinarith), 
                mul_pos hb (show (0 : ℝ) < a * c by nlinarith), 
                mul_pos hc (show (0 : ℝ) < a * b by nlinarith),
                mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
                ]
    · -- Show that the denominator is positive 
      positivity
  linarith