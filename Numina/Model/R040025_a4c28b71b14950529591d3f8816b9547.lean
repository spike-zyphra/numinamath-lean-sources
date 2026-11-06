import Mathlib

theorem inequalities_327413 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = a * b) :
    a / (b^2 + 4) + b / (a^2 + 4) ≥ 1 / 2 := by 

  have h8 : a / (b^2 + 4) + b / (a^2 + 4) - 1 / 2 ≥ 0 := by 
    have h9 : 0 < (b ^ 2 + 4) * (a ^ 2 + 4) := by positivity
    have h90 : a / (b^2 + 4) + b / (a^2 + 4) - 1 / 2 =
        (2 * a * (a ^ 2 + 4) + 2 * b * (b ^ 2 + 4) - ( (b ^ 2 + 4) * (a ^ 2 + 4) ) ) / (2 * (b ^ 2 + 4) * (a ^ 2 + 4)) := by 
      field_simp 
      ring
    rw [h90] at *
    have h91 : 0 < 2 * (b ^ 2 + 4) * (a ^ 2 + 4) := by positivity
    have h92 : (b - 2) ^ 2 ≥ 0 := sq_nonneg (b - 2)
    have h93 : (a - 2) ^ 2 ≥ 0 := sq_nonneg (a - 2)
    have h94 : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
    have h95 : b * (b - 2) ^ 2 ≥ 0 := by positivity
    have h96 : a * (a - 2) ^ 2 ≥ 0 := by positivity
    have h97 : a * b ≥ 0 := by positivity 
    -- Final of `by` states top level true.
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2), sq_nonneg (b - 2),
      h, sq_nonneg (a * b - 4), sq_nonneg (a ^ 2 - b ^ 2), mul_pos ha (show 0 < b by linarith)]
    positivity

  linarith