import Mathlib.Tactic

theorem inequalities_185281
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (a^3 / (a^2 + a * b + b^2) + b^3 / (b^2 + b * c + c^2) +
     c^3 / (c^2 + c * a + a^2)) ≥
    (a + b + c) / 3 := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha
  have h4 : 0 < a^2 + a * b + b^2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have h5 : 0 < b^2 + b * c + c^2 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]
  have h6 : 0 < c^2 + c * a + a^2 := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a)]
  have h7 : a^3 / (a^2 + a * b + b^2) ≥ (2 * a - b) / 3 := by
    have h8 : a^2 + a * b + b^2 > 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    apply (le_div_iff₀ h8).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb, mul_pos ha (show 0 < b * b by nlinarith)]
  have h10 : b^3 / (b^2 + b * c + c^2) ≥ (2 * b - c) / 3 := by
    have h11 : b^2 + b * c + c^2 > 0 := by nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]
    apply (le_div_iff₀ h11).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b - c), sq_nonneg (b + c), mul_pos hb hc, mul_pos hb (show 0 < c * c by nlinarith)]
  have h12 : c^3 / (c^2 + c * a + a^2) ≥ (2 * c - a) / 3 := by
    have h13 : c^2 + c * a + a^2 > 0 := by nlinarith [sq_nonneg (c - a), sq_nonneg (c + a)]
    apply (le_div_iff₀ h13).mpr
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c - a), sq_nonneg (c + a), mul_pos hc ha, mul_pos hc (show 0 < a * a by nlinarith)]
  have h14 : a^3 / (a^2 + a * b + b^2) + b^3 / (b^2 + b * c + c^2) + c^3 / (c^2 + c * a + a^2) ≥ (a + b + c) / 3 := by
    linarith [h7, h10, h12]
  linarith [h14]