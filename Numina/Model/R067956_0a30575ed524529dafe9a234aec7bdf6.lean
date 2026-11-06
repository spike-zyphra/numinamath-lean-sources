import Mathlib

theorem inequalities_601725 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    8 ≤ 1 / a ^ 2 + 1 / b ^ 2 := by 
  have h1 : b = 1 - a := by linarith
  rw [h1] at *
  have h01 : a > 0 := ha
  have h02 : 1 - a > 0 := by nlinarith
  have h3 : 1 / a ^ 2 + 1 / (1 - a) ^ 2 - 8 ≥ 0 := by
    have pos1 : 0 < a := ha
    have pos2 : 0 < 1 - a := by nlinarith 
    have h4 : 1 / a ^ 2 + 1 / (1 - a) ^ 2 - 8 = ( (1 - a) ^ 2 + a ^ 2 - 8 * ( a ^ 2 * (1 - a) ^ 2 ) ) / ( a ^ 2 * (1 - a) ^ 2 ) := by 
      field_simp
      <;> ring_nf <;> field_simp <;> ring
      <;> field_simp <;> ring
    rw [h4]
    have h5 : 0 < a ^ 2 * (1 - a) ^ 2 := mul_pos (sq_pos_of_pos h01) (sq_pos_of_pos h02)
    have h6 : (1 - a) ^ 2 + a ^ 2 - 8 * ( a ^ 2 * (1 - a) ^ 2 ) ≥ 0 := by
      nlinarith [sq_nonneg (a ^ 2 * (1 - a) ^ 2), sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), sq_nonneg (a * (1 - a) - 1 / 4), h01, h02, mul_pos ha (show 0 < 1 - a by nlinarith)]
    have h7 : ( (1 - a) ^ 2 + a ^ 2 - 8 * ( a ^ 2 * (1 - a) ^ 2 ) ) / ( a ^ 2 * (1 - a) ^ 2 ) ≥ 0 := by 
      apply div_nonneg 
      linarith 
      nlinarith 
    linarith 
  linarith [h3]