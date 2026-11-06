import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_107290 (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a + b > c)
    (h₂ : b + c > a)
    (h₃ : c + a > b)
    (h₄ : a + b + c = 2) :
    a^2 + b^2 + c^2 < 2 * (1 - a * b * c) := by
  rcases h₀ with ⟨ha, hb, hc⟩
  nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), 
          mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₃), 
          mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃), 
          h₄, 
          mul_pos ha (show 0 < b * c by nlinarith)
          ]