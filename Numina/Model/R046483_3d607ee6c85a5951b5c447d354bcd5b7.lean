import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_4256
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b > c)
  (h₂ : a + c > b)
  (h₃ : b + c > a) :
  3 * (a^2 + b^2 + c^2) / (a + b + c)^2 +
  (a * b + b * c + c * a) / (a^2 + b^2 + c^2) ≤ 2 := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have h4 : 0 < a + b + c := by linarith
  have h5 : 0 < a^2 + b^2 + c^2 := by nlinarith
  have h : 3 * (a^2 + b^2 + c^2) / (a + b + c) ^ 2 + (a * b + b * c + c * a) / (a^2 + b^2 + c^2) - 2 ≤ 0 := by
    have h6 : 0 < (a + b + c)^2 := by positivity
    have h7 : 0 < a^2 + b^2 + c^2 := h5
    have h8 : 3 * (a^2 + b^2 + c^2) / (a + b + c) ^ 2 + (a * b + b * c + c * a) / (a^2 + b^2 + c^2) - 2 =
        (3 * (a^2 + b^2 + c^2) * (a^2 + b^2 + c^2) + (a * b + b * c + c * a) * (a + b + c)^2 - 2 * (a + b + c)^2 * (a^2 + b^2 + c^2)) / ((a + b + c)^2 * (a^2 + b^2 + c^2)) := by
      field_simp
      <;> ring
    rw [h8]
    have h9 : 0 < (a + b + c) ^ 2 * (a^2 + b^2 + c^2) := by positivity
    have h10 : 3 * (a^2 + b^2 + c^2) * (a^2 + b^2 + c^2) + (a * b + b * c + c * a) * (a + b + c)^2 - 2 * (a + b + c)^2 * (a^2 + b^2 + c^2) ≤ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), 
        mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃), 
        mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₃)
      ]
    apply div_nonpos_of_nonpos_of_nonneg h10 (by positivity)
  linarith