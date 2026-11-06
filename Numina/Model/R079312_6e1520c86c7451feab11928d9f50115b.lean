import Mathlib

theorem inequalities_318310 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) +
    c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 := by 
  have h1 : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ c / (a + b + c) := by
    have h11 : a ^ 5 + b ^ 5 ≥ a ^ 2 * b ^ 2 * (a + b) := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2), sq_nonneg (b ^ 2), mul_pos ha hb]
    have h12 : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ 1 / (a * b * (a + b) + 1) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b - b * a), h11, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h13 : 1 / (a * b * (a + b) + 1) ≤ c / (a + b + c) := by 
      have h14 : 0 < a * b := mul_pos ha hb
      have h15 : a * b * (a + b) + 1 > 0 := by positivity
      have h16 : a + b + c > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]
    linarith [h12, h13]

  have h4 : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (a + b + c) := by 
    have h21 : b ^ 5 + c ^ 5 ≥ b ^ 2 * c ^ 2 * (b + c) := by 
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b ^ 2), sq_nonneg (c ^ 2), mul_pos hb hc]
    have h22 : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ 1 / (b * c * (b + c) + 1) := by 
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b * c - c * b), h21, mul_pos hb hc, mul_pos hb ha, mul_pos ha hc]
    have h23 : 1 / (b * c * (b + c) + 1) ≤ a / (a + b + c) := by 
      have h24 : 0 < b * c := mul_pos hb hc
      have h25 : b * c * (b + c) + 1 > 0 := by positivity
      have h26 : a + b + c > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [sq_nonneg (b * c - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (a - 1), 
          mul_pos hb hc, mul_pos hb ha, mul_pos ha hc, habc]
    linarith [h22, h23]

  have h5 : c * a / (c ^ 5 + a ^ 5 + c * a) ≤ b / (a + b + c) := by 
    have h31 : c ^ 5 + a ^ 5 ≥ c ^ 2 * a ^ 2 * (c + a) := by 
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c ^ 2), sq_nonneg (a ^ 2), mul_pos hc ha]
    have h32 : c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 / (c * a * (c + a) + 1) := by 
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c * a - a * c), h31, mul_pos hc ha, mul_pos ha hb, mul_pos ha hc]
    have h33 : 1 / (c * a * (c + a) + 1) ≤ b / (a + b + c) := by 
      have h34 : 0 < c * a := mul_pos hc ha
      have h35 : c * a * (c + a) + 1 > 0 := by positivity
      have h36 : a + b + c > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [sq_nonneg (c * a - 1), sq_nonneg (c - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), 
          mul_pos hc ha, mul_pos hb ha, mul_pos hb hc, habc]
    linarith [h32, h33]

  have h6 : a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) + c * a / (c ^ 5 + a ^ 5 + c * a) ≤ c / (a + b + c) + a / (a + b + c) + b / (a + b + c) := by 
    linarith [h1, h4, h5]

  have h7 : c / (a + b + c) + a / (a + b + c) + b / (a + b + c) = 1 := by
    field_simp
    <;> nlinarith [habc]

  linarith [h6, h7]