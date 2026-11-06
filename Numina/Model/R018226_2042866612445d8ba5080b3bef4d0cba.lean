import Mathlib

theorem inequalities_601594
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (h : a * b * c * d = 1) :
    1 ≤ 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 + 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 := by

  have h1 : 0 < a * b := by
    nlinarith
  have h2 : 0 < c * d := by
    nlinarith [h, mul_pos ha hb, mul_pos hc hd]
  have h3 : (a * b) * (c * d) = 1 := by 
    nlinarith

  have h4 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 ≥ 1 / (1 + a * b) := by 
    have h5 : 0 < (1 + a) ^ 2 := by
      nlinarith
    have h6 : 0 < (1 + b) ^ 2 := by
      nlinarith 
    have h7 : 0 < (1 + a * b) := by 
      nlinarith [mul_pos ha hb]
    have h8 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 - 1 / (1 + a * b) ≥ 0 := by 
      have h9 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 - 1 / (1 + a * b) = 
          ( (1 + a * b) * (1 + b) ^ 2 + (1 + a * b) * (1 + a) ^ 2 - (1 + a) ^ 2 * (1 + b) ^ 2 ) / ( (1 + a) ^ 2 * (1 + b) ^ 2 * (1 + a * b) ) := by 
        field_simp 
        <;> ring 
      rw [h9] at *
      have h10 : (1 + a * b) * (1 + b) ^ 2 + (1 + a * b) * (1 + a) ^ 2 - (1 + a) ^ 2 * (1 + b) ^ 2 ≥ 0 := by 
        nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), 
                mul_pos ha hb ]
      have h11 : (1 + a) ^ 2 * (1 + b) ^ 2 * (1 + a * b) > 0 := by
        positivity 
      have h12 : ( (1 + a * b) * (1 + b) ^ 2 + (1 + a * b) * (1 + a) ^ 2 - (1 + a) ^ 2 * (1 + b) ^ 2 ) / ( (1 + a) ^ 2 * (1 + b) ^ 2 * (1 + a * b) ) ≥ 0 := by 
        apply div_nonneg 
        linarith 
        linarith 
      linarith 
      all_goals positivity 
    linarith

  have h5 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 ≥ 1 / (1 + c * d) := by 
    have h5 : 0 < (1 + c) ^ 2 := by
      nlinarith 
    have h6 : 0 < (1 + d) ^ 2 := by
      nlinarith 
    have h7 : 0 < (1 + c * d) := by
      nlinarith [mul_pos hc hd]
    have h8 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 - 1 / (1 + c * d) ≥ 0 := by 
      have h9 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 - 1 / (1 + c * d) = 
          ( (1 + c * d) * (1 + d) ^ 2 + (1 + c * d) * (1 + c) ^ 2 - (1 + c) ^ 2 * (1 + d) ^ 2 ) / ( (1 + c) ^ 2 * (1 + d) ^ 2 * (1 + c * d) ) := by 
        field_simp 
        <;> ring 
      rw [h9] at *
      have h10 : (1 + c * d) * (1 + d) ^ 2 + (1 + c * d) * (1 + c) ^ 2 - (1 + c) ^ 2 * (1 + d) ^ 2 ≥ 0 := by 
        nlinarith [sq_nonneg (c * d - 1), sq_nonneg (c - d), sq_nonneg (c - 1), sq_nonneg (d - 1), 
                mul_pos hc hd ]
      have h11 : (1 + c) ^ 2 * (1 + d) ^ 2 * (1 + c * d) > 0 := by
        positivity 
      have h12 : ( (1 + c * d) * (1 + d) ^ 2 + (1 + c * d) * (1 + c) ^ 2 - (1 + c) ^ 2 * (1 + d) ^ 2 ) / ( (1 + c) ^ 2 * (1 + d) ^ 2 * (1 + c * d) ) ≥ 0 := by 
        apply div_nonneg 
        linarith 
        linarith 
      linarith 
      all_goals positivity 
    linarith

  have h6 : 1 / (1 + a * b) + 1 / (1 + c * d) = 1 := by
    have h7 : (a * b) * (c * d) = 1 := by 
      nlinarith 
    have h8 : a * b > 0 := by 
      nlinarith 
    have h9 : c * d > 0 := by 
      nlinarith 
    field_simp [h7] 
    <;> nlinarith
  
  linarith [h4, h5, h6]