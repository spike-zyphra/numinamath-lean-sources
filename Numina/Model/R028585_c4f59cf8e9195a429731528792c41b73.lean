import Mathlib.Tactic

theorem inequalities_125165 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) ≥ a + b + c := by

  have h1 : 0 < a * b * c := by
    positivity

  have h2 : a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) - (a + b + c) ≥ 0 := by

    have h3 : a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) - (a + b + c) =
        (a ^ 4 + b ^ 4 + c ^ 4 - (a + b + c) * (a * b * c)) / (a * b * c) := by 
      field_simp 
      ring 
    rw [h3] at *
  
    have h4 : a ^ 4 + b ^ 4 + c ^ 4 ≥ a * b * c * (a + b + c) := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - c ^ 2), 
                  sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
                  sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
                  sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
                  sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

    have h5 : a ^ 4 + b ^ 4 + c ^ 4 - (a + b + c) * (a * b * c) ≥ 0 := by linarith
  
    have h6 : (a ^ 4 + b ^ 4 + c ^ 4 - (a + b + c) * (a * b * c)) / (a * b * c) ≥ 0 := by 
      apply div_nonneg 
      linarith 
      positivity
  
    linarith

  linarith