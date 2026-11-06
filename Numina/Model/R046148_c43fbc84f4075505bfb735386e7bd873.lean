import Mathlib

open Real
theorem algebra_315143 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : 1 / b - 1 / a = 1) :
    1 / (1 - b / 2) < 1 / sqrt (1 - b) ∧
    1 / sqrt (1 - b) = sqrt (1 + a) ∧
    sqrt (1 + a) < 1 + a / 2 := by

  have h1 : a - b = a * b := by
    field_simp [(show b ≠ 0 by linarith), (show a ≠ 0 by linarith)] at h 
    linarith

  have h2 : 0 < 1 - b := by
    nlinarith [show 0 < a by linarith, sq_nonneg (a - b - a * b), h1]

  have h3 : 1 + a = 1 / (1 - b) := by 
    have h4 : a = b / (1 - b) := by 
      have : 1 - b > 0 := by linarith 
      field_simp at * 
      nlinarith [h1, sq_nonneg (a * b), sq_nonneg (a - b)]
    rw [h4]
    field_simp 
    <;> nlinarith

  have h4 : (sqrt (1 + a)) ^ 2 = 1 + a := Real.sq_sqrt (by linarith)

  have h_eq : 1 / sqrt (1 - b) = sqrt (1 + a) := by
    have h5 : 1 / sqrt (1 - b) = Real.sqrt (1 / (1 - b)) := by 
      field_simp 
      all_goals linarith 
    have h6 : Real.sqrt (1 / (1 - b)) = Real.sqrt (1 + a) := by 
      rw [show 1 / (1 - b) = 1 + a by linarith [h3] ]
    rw [h5, h6]

  have h5 : 0 < 1 - b / 2 := by
    nlinarith [hb, show b < 1 by nlinarith [show 0 < a by linarith, sq_nonneg (a - b - a * b), h1] ]

  have h6 : 1 / (1 - b / 2) < 1 / sqrt (1 - b) := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg (1 - b), Real.sq_sqrt (show 0 ≤ (1 - b : ℝ) by linarith), sq_nonneg (Real.sqrt (1 - b) - (1 - b / 2) ), Real.sqrt_nonneg (1 - b), Real.sq_sqrt (show 0 ≤ (1 - b : ℝ) by linarith) ]

  have h8 : sqrt (1 + a) < 1 + a / 2 := by
    nlinarith [Real.sqrt_nonneg (1 + a), Real.sq_sqrt (show 0 ≤ (1 + a : ℝ) by linarith), sq_pos_of_pos ha, mul_pos (show (0 : ℝ) < (1 + a) by linarith) (show (0 : ℝ) < (1 + a / 2) by linarith) ]

  constructor
  · exact h6
  constructor
  · exact h_eq 
  · exact h8