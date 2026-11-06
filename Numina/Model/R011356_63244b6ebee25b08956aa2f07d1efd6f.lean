import Mathlib

open Real

theorem inequalities_262438 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) : (1 + a) / (1 + a + a * b) + (1 + b) / (1 + b + b * c) +
      (1 + c) / (1 + c + c * a) = 2 := by
  have h1 : a * b * c = 1 := habc
  have h2 : a * b > 0 := mul_pos ha hb
  have h3 : a * c > 0 := mul_pos ha hc
  have h4 : b * c > 0  := mul_pos hb hc
  have h5 : a * b * c > 0  := mul_pos (mul_pos ha hb) hc
  have eq1 : (1 + a) / (1 + a + a * b) + (1 + b) / (1 + b + b * c) + (1 + c) / (1 + c + c * a) - 2 = 0 := by
    have eq2 : (1 + a) / (1 + a + a * b) + (1 + b) / (1 + b + b * c) + (1 + c) / (1 + c + c * a) - 2 =
        ((1 + a) * (1 + b + b * c) * (1 + c + c * a) + (1 + b) * (1 + a + a * b) * (1 + c + c * a) + (1 + c) * (1 + a + a * b) * (1 + b + b * c) - 2 * (1 + a + a * b) * (1 + b + b * c) * (1 + c + c * a)) / ((1 + a + a * b) * (1 + b + b * c) * (1 + c + c * a)) := by
      field_simp
      <;> ring
    rw [eq2] at *
    have h6 : ( (1 + a) * (1 + b + b * c) * (1 + c + c * a) + (1 + b) * (1 + a + a * b) * (1 + c + c * a) + (1 + c) * (1 + a + a * b) * (1 + b + b * c) - 2 * (1 + a + a * b) * (1 + b + b * c) * (1 + c + c * a) ) = 0 := by
      rw [show c = 1 / (a * b) by
        field_simp [h1]
        <;> nlinarith [h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc] ]
      field_simp [h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      <;> nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * b * c - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    rw [h6]
    norm_num
  linarith