import Mathlib

theorem inequalities_600080 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) +
    (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ≥
    a^2 + b^2 + c^2 + d^2 := by
  have h1 : 0 < a + b + c := by linarith
  have h2 : 0 < b + c + d := by linarith
  have h3 : 0 < c + d + a := by linarith
  have h4 : 0 < d + a + b := by linarith
  have h11 : (a^3 + b^3 + c^3) / (a + b + c) ≥ (a^2 + b^2 + c^2) / 3 := by
    have hx1 : 0 < a + b + c := by linarith 
    apply (le_div_iff₀ hx1).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h12 : (b^3 + c^3 + d^3) / (b + c + d) ≥ (b^2 + c^2 + d^2) / 3 := by
    have hx2 : 0 < b + c + d := by linarith
    apply (le_div_iff₀ hx2).mpr 
    nlinarith [sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - b),
      sq_nonneg (b + c + d), mul_pos hb hc, mul_pos hc hd, mul_pos hb hd]
  have h13 : (c^3 + d^3 + a^3) / (c + d + a) ≥ (c^2 + d^2 + a^2) / 3 := by
    have hx3 : 0 < c + d + a := by linarith 
    apply (le_div_iff₀ hx3).mpr 
    nlinarith [sq_nonneg (c - d), sq_nonneg (d - a), sq_nonneg (a - c),
      sq_nonneg (c + d + a), mul_pos hc hd, mul_pos hd ha, mul_pos hc ha]
  have h14 : (d^3 + a^3 + b^3) / (d + a + b) ≥ (d^2 + a^2 + b^2) / 3 := by 
    have hx4 : 0 < d + a + b := by linarith 
    apply (le_div_iff₀ hx4).mpr 
    nlinarith [sq_nonneg (d - a), sq_nonneg (a - b), sq_nonneg (b - d), 
      sq_nonneg (d + a + b), mul_pos hd ha, mul_pos ha hb, mul_pos hd hb]
  linarith [h11, h12, h13, h14]