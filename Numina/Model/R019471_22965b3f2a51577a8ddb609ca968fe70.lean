import Mathlib

open Real
open scoped BigOperators

theorem inequalities_155414 (a b c h : ℝ)
  (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a^2 + b^2 = c^2) (h₄ : h = (a * b) / c) :
  a + b < c + h := by
  rw [h₄]
  have h6 : c > a := by
    nlinarith [sq_pos_of_pos h₀, sq_pos_of_pos h₁, h₃]
  have h7 : c > b := by
    nlinarith [sq_pos_of_pos h₀, sq_pos_of_pos h₁, h₃]
  have h8 : (c - a) * (c - b) > 0 := by
    apply mul_pos
    all_goals linarith
  have h9 : c ^ 2 - (a * c + b * c) + (a * b) > 0 := by
    have h10 : (c - a) * (c - b) = c^2 - (a * c + b * c) + (a * b) := by 
      ring
    linarith [h8, h10]
  have h10 : a + b < c + (a * b / c) := by
    have h11 : c * (a + b) < c^2 + a * b := by
      nlinarith
    have h12 : a + b < (c^2 + a * b)/c := by
      apply (lt_div_iff' (by positivity)).mpr
      nlinarith
    have h13 : (c^2 + a * b) / c = c + (a * b / c) := by
      field_simp
      <;> ring
    linarith [h12, h13]
  linarith [h10]