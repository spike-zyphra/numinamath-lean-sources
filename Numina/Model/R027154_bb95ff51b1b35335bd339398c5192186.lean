import Mathlib

theorem inequalities_602908 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 1) :
    a / (1 + a) + b / (1 + b) ≤ 5 / (6 * (1 + a * b)) := by 
  have h1 : 0 < a * b := by nlinarith
  have h2 : 0 < 1 + a := by nlinarith
  have h3 : 0 < 1 + b := by nlinarith
  have h4 : 0 < 6 * (1 + a * b) := by positivity
  have h5 : a / (1 + a) + b / (1 + b) - 5 / (6 * (1 + a * b)) ≤ 0 := by
    have pos1 : 0 < (1 + a) * (1 + b) * (6 * (1 + a * b)) := by positivity
    have h7 : a / (1 + a) + b / (1 + b) - 5 / (6 * (1 + a * b)) =
        ( (a * (1 + b) * (6 * (1 + a * b)) ) + (b * (1 + a) * (6 * (1 + a * b)) ) - (5 * (1 + a) * (1 + b) ) ) / ( (1 + a) * (1 + b) * (6 * (1 + a * b)) ) := by 
      field_simp
      <;> ring
    rw [h7]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Numerator ≤ 0
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), 
          h, mul_pos ha hb, mul_pos ha h2, mul_pos ha h3, 
          mul_pos hb h2, mul_pos hb h3, 
          h1, sq_nonneg (a * b - 1 / 4), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)]
    · -- Denominator > 0
      positivity
  linarith