import Mathlib
theorem inequalities_317211 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h : a * b * c * d = 1) :
1 ≤ 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 + 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2:= by
  have h1 : 0 < (1 + a) * (1 + b) := by positivity
  have h2 : 0 < (1 + c) * (1 + d) := by positivity
  have h3 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 ≥ 1 / (1 + a * b) := by
    have h4 : 0 < (1 + a) * (1 + b) := by positivity
    have h5 : 0 < 1 + a * b := by
      nlinarith
    have h6 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 - 1 / (1 + a * b) ≥ 0 := by
      have h7 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 - 1 / (1 + a * b) = 
        ( (1 + b) ^ 2 * (1 + a * b) + (1 + a) ^ 2 * (1 + a * b) - (1 + a) ^ 2 * (1 + b) ^ 2 ) / ( (1 + a) ^ 2 * (1 + b) ^ 2 * (1 + a * b) ) := by
        field_simp
        <;> ring
      rw [h7]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), mul_pos ha hb
      ]
      all_goals positivity
    linarith
  have h4 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 ≥ 1 / (1 + c * d) := by
    have h4 : 0 < (1 + c) * (1 + d) := by positivity
    have h5 : 0 < 1 + c * d := by
      nlinarith
    have h6 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 - 1 / (1 + c * d) ≥ 0 := by
      have h7 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 - 1 / (1 + c * d) = 
        ( (1 + d) ^ 2 * (1 + c * d) + (1 + c) ^ 2 * (1 + c * d) - (1 + c) ^ 2 * (1 + d) ^ 2 ) / ( (1 + c) ^ 2 * (1 + d) ^ 2 * (1 + c * d) ) := by
        field_simp
        <;> ring
      rw [h7]
      apply div_nonneg
      nlinarith [sq_nonneg (c * d - 1), sq_nonneg (c - d), sq_nonneg (c - 1), sq_nonneg (d - 1), mul_pos hc hd
      ]
      all_goals positivity
    linarith
  have h4a : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 + 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 ≥ 1 / (1 + a * b) + 1 / (1 + c * d) := by 
    linarith [h3, h4]
  have h5 : 1 / (1 + a * b) + 1 / (1 + c * d) ≥ 1 := by
    have h6 : a * b * c * d = 1 := h
    have h7 : 0 < 1 + a * b := by
      nlinarith [mul_pos ha hb]
    have h8 : 0 < 1 + c * d := by
      nlinarith [mul_pos hc hd]
    have h9 : a * b * (c * d) = 1 := by
      nlinarith
    have h8 : 1 / (1 + a * b) + 1 / (1 + c * d) - 1 ≥ 0 := by
      have h13 : 1 / (1 + a * b) + 1 / (1 + c * d) - 1 = ( (1 + c * d) + (1 + a * b) - (1 + a * b) * (1 + c * d) ) / ( (1 + a * b) * (1 + c * d) ) := by
        field_simp
        <;> ring
      rw [h13]
      have h14 : ( (1 + c * d) + (1 + a * b) - (1 + a * b) * (1 + c * d) ) ≥ 0 := by
        nlinarith [ h9, sq_nonneg ( (a * b) - 1 ), sq_nonneg ( (c * d) - 1 ), mul_pos (show 0 < a * b by positivity) (show 0 < c * d by positivity ), h
        ]
      apply div_nonneg 
      nlinarith
      all_goals nlinarith
    linarith 
  linarith [h4a, h5]