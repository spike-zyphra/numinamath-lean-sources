import Mathlib

open Real

theorem inequalities_3826 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a ^ (b / (a + b + c)) * b ^ (c / (a + b + c)) * c ^ (a / (a + b + c)) ≤ (a * b + b * c + c * a) / (a + b + c) := by

  have h1 : a + b + c > 0 := by linarith
  have h2 : b / (a + b + c) + c / (a + b + c) + a / (a + b + c) = 1 := by
    field_simp
    <;> linarith

  have h8 : a ^ (b / (a + b + c)) * b ^ (c / (a + b + c)) * c ^ (a / (a + b + c)) ≤
          (b / (a + b + c) * a + c / (a + b + c) * b + a / (a + b + c) * c) := by
    have h4' : b / (a + b + c) + c / (a + b + c) + a / (a + b + c) = 1 := h2
    have h5 : b / (a + b + c) ≥ 0 := by
      apply div_nonneg
      linarith
      linarith
    have h6 : c / (a + b + c) ≥ 0 := by
      apply div_nonneg
      linarith
      linarith
    have h7 : a / (a + b + c) ≥ 0 := by
      apply div_nonneg
      linarith
      linarith
    have h14 : a > 0 := by linarith
    have h15 : b > 0 := by linarith
    have h16 : c > 0 := by linarith
    have h17 : a ^ (b / (a + b + c)) * b ^ (c / (a + b + c)) * c ^ (a / (a + b + c)) ≤
        (b / (a + b + c) * a + c / (a + b + c) * b + a / (a + b + c) * c) := by
      apply Real.geom_mean_le_arith_mean3_weighted
      all_goals
      try linarith
      all_goals
      try positivity
    linarith

  have h9 : b / (a + b + c) * a + c / (a + b + c) * b + a / (a + b + c) * c = 
          (a * b + b * c + c * a) / (a + b + c) := by
    field_simp
    <;> ring

  linarith [h8, h9]