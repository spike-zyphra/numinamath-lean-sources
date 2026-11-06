import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem inequalities_146699
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d) :
    1/(1/a + 1/b) + 1/(1/c + 1/d) ≤ 1/(1/(a + c) + 1/(b + d)) := by
  have ha1 : 0 < a * b := mul_pos ha hb
  have hb1 : 0 < a * b := mul_pos ha hb
  have ha2 : 0 < a * b * c * d := by positivity
  have ha3 : 0 < a + b := by linarith
  have hc1 : 0 < c + d := by linarith
  have hd1 : 0 < (a + c) * (b + d) := by positivity

  have h1 : 1 / (1 / a + 1 / b) = a * b / (a + b) := by
    field_simp
    <;> nlinarith
  
  have h2 : 1 / (1 / c + 1 / d) = c * d / (c + d) := by
    field_simp
    <;> nlinarith
  
  have h3 : 1 / (1 / (a + c) + 1 / (b + d)) = (a + c) * (b + d) / (a + b + c + d) := by 
    field_simp 
    <;> nlinarith
  
  rw [h1, h2, h3]

  have ha4 : 0 < a * b := by positivity
  have hb4 : 0 < c * d := by positivity
  have hc4 : 0 < a + b := by positivity
  have hd4 : 0 < c + d := by positivity
  have he4 : 0 < a + b + c + d := by positivity
  
  have h4 : a * b / (a + b) + c * d / (c + d) - (a + c) * (b + d) / (a + b + c + d) ≤ 0 := by

    have h5 : 0 < (a + b) * (c + d) * (a + b + c + d) := by positivity
    have h6 : a * b / (a + b) + c * d / (c + d) - (a + c) * (b + d) / (a + b + c + d) = 
      ( a * b * (c + d) * (a + b + c + d) + c * d * (a + b) * (a + b + c + d) - (a + c) * (b + d) * ( (a + b) * (c + d) ) ) / ( (a + b) * (c + d) * (a + b + c + d) ) := by
      field_simp
      ring

    rw [h6]
    apply div_nonpos_of_nonpos_of_nonneg
    -- Numerator non-positive
    nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * d - b * c), sq_nonneg (a - b), sq_nonneg (c - d), 
              sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c), sq_nonneg (a * (c - d) - b * (c - d)), 
              sq_nonneg ((a * c - b * d) - (a * d - b * c)), 
              mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
              mul_pos hb hc, mul_pos hb hd, 
              mul_pos hc hd ]
    -- Denominator non-negative 
    all_goals
      positivity
  
  linarith