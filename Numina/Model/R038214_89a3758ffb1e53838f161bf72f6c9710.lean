import Mathlib

theorem inequalities_205081 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    (a^4 + 3 * a * b^3) / (a^3 + 2 * b^3) + (b^4 + 3 * b * c^3) / (b^3 + 2 * c^3) +
    (c^4 + 3 * c * a^3) / (c^3 + 2 * a^3) ≤ 4 := by

  have h1 : (a^4 + 3 * a * b^3) / (a^3 + 2 * b^3) = a + (a * b^3) / (a^3 + 2 * b^3) := by
    field_simp
    ring
  
  have h2 : (b^4 + 3 * b * c^3) / (b^3 + 2 * c^3) = b + (b * c^3) / (b^3 + 2 * c^3) := by 
    field_simp 
    ring
  
  have h3 : (c^4 + 3 * c * a^3) / (c^3 + 2 * a^3) = c + (c * a^3) / (c^3 + 2 * a^3) := by 
    field_simp 
    ring
  
  rw [h1, h2, h3]

  have h4 : (a * b^3) / (a^3 + 2 * b^3) ≤ b / 3 := by 
    have h21 : a^3 + 2 * b^3 ≥ 3 * a * b^2 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 - b^2), 
        sq_nonneg (a - 2 * b), sq_nonneg (b - 2 * a), sq_nonneg (a * b), 
          pow_two_nonneg (a - b), pow_two_nonneg (a + b), 
            mul_pos ha hb, mul_pos ha (show 0 < a^2 by positivity), mul_pos hb (show 0 < b^2 by positivity)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [h21, mul_pos ha hb, mul_pos ha (show 0 < b^2 by positivity), sq_nonneg (a - b)]
  
  have h5 : (b * c^3) / (b^3 + 2 * c^3) ≤ c / 3 := by 
    have h21 : b^3 + 2 * c^3 ≥ 3 * b * c^2 := by 
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b^2 - c^2), 
        sq_nonneg (b - 2 * c), sq_nonneg (c - 2 * b), sq_nonneg (b * c), 
          pow_two_nonneg (b - c), pow_two_nonneg (b + c), 
            mul_pos hb hc, mul_pos hb (show 0 < b^2 by positivity), mul_pos hc (show 0 < c^2 by positivity)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [h21, mul_pos hb hc, mul_pos hb (show 0 < c^2 by positivity), sq_nonneg (b - c)]
  
  have h6 : (c * a^3) / (c^3 + 2 * a^3) ≤ a / 3 := by 
    have h21 : c^3 + 2 * a^3 ≥ 3 * c * a^2 := by 
      nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c^2 - a^2), 
        sq_nonneg (c - 2 * a), sq_nonneg (a - 2 * c), sq_nonneg (c * a), 
          pow_two_nonneg (c - a), pow_two_nonneg (c + a), 
            mul_pos hc ha, mul_pos hc (show 0 < c^2 by positivity), mul_pos ha (show 0 < a^2 by positivity)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [h21, mul_pos hc ha, mul_pos hc (show 0 < a^2 by positivity), sq_nonneg (c - a)]
  
  have h7 : a + b + c ≤ 3 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h, 
      sq_nonneg (a + b + c - 3), sq_nonneg (a^2 + b^2 + c^2 - 3)]
  
  linarith [h4, h5, h6, h7]