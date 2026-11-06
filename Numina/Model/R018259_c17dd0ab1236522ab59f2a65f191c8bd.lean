import Mathlib

open Real

theorem inequalities_231882 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥
    sqrt 3 + a * b / (a + b) + b * c / (b + c) + c * a / (c + a) := by
  have h1 : sqrt 3 ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h2 : sqrt 3 > 0 := by
    positivity
  have h6 : (a + b + c) ^ 2 ≥ 3 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      h, mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]
  have h62 : a + b + c ≥ sqrt 3 := by 
    have h7 : sqrt 3 > 0 := by positivity
    have h8 : (a + b + c) ^ 2 ≥ 3 := h6
    have h9 : (sqrt 3) ^ 2 = 3 := h1
    have h10 : a + b + c ≥ 0 := by positivity
    have h11 : sqrt 3 ≥ 0 := by positivity
    nlinarith [sq_nonneg ((a + b + c) - sqrt 3), Real.sqrt_nonneg 3]
  have eq1 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - (sqrt 3 + a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) = (a + b + c) - sqrt 3 := by 
    field_simp 
    <;> nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h, h1]
  have h7 : (a + b + c) - sqrt 3 ≥ 0 := by 
    linarith [h62]
  have h8 : (1 / (a + b) + 1 / (b + c) + 1 / (c + a) - (sqrt 3 + a * b / (a + b) + b * c / (b + c) + c * a / (c + a))) ≥ 0 := by 
    linarith [eq1, h7]
  linarith [h8]