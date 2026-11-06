import Mathlib

theorem inequalities_598701 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) +
    (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ≥
    a^2 + b^2 + c^2 + d^2 := by
  have h₁ : a + b + c > 0 := by positivity
  have h₂ : b + c + d > 0 := by positivity
  have h₃ : c + d + a > 0 := by positivity
  have h₄ : d + a + b > 0 := by positivity

  have h5 : (a^3 + b^3 + c^3) / (a + b + c) ≥ (a^2 + b^2 + c^2)/3 := by
    have h₄ : a + b + c > 0 := by positivity
    apply (le_div_iff₀ h₄).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b + c),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h6 : (b^3 + c^3 + d^3) / (b + c + d) ≥ (b^2 + c^2 + d^2)/3 := by
    have h₄ : b + c + d > 0 := by positivity
    apply (le_div_iff₀ h₄).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (b + c + d),
      mul_pos hb hc, mul_pos hc hd, mul_pos hb hd]

  have h7 : (c^3 + d^3 + a^3) / (c + d + a) ≥ (c^2 + d^2 + a^2)/3 := by
    have h₄ : c + d + a > 0 := by positivity
    apply (le_div_iff₀ h₄).mpr
    nlinarith [sq_nonneg (c - d), sq_nonneg (c - a), sq_nonneg (d - a), sq_nonneg (c + d + a),
      mul_pos ha hc, mul_pos ha hd, mul_pos hc hd]

  have h8 : (d^3 + a^3 + b^3) / (d + a + b) ≥ (d^2 + a^2 + b^2)/3 := by
    have h₄ : d + a + b > 0 := by positivity
    apply (le_div_iff₀ h₄).mpr
    nlinarith [sq_nonneg (d - a), sq_nonneg (d - b), sq_nonneg (a - b), sq_nonneg (d + a + b),
      mul_pos ha hb, mul_pos ha hd, mul_pos hb hd]

  linarith [h5, h6, h7, h8]