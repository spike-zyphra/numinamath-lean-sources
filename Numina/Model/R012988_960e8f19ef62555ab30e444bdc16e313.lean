import Mathlib

theorem inequalities_598613 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    3 / 2 ≤ 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha
  have h4 : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) - 3 / 2 ≥ 0 := by
    have hab1 : a * b + b * c + c * a ≤ 3 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h6 : 1 / (1 + a * b) ≥ (3 - a*b) / 4 := by
      have h7 : 0 < 1 + a * b := by nlinarith 
      apply (le_div_iff₀ h7).mpr 
      nlinarith [sq_nonneg (a*b - 1), h, sq_nonneg (a-c), sq_nonneg (b-c), mul_pos ha hb, sq_nonneg (a-b), sq_nonneg (a*c - b*c), sq_nonneg (a*c - a*b), sq_nonneg (b*c - a*b)]
    have h7 : 1 / (1 + b * c) ≥ (3 - b*c) / 4 := by
      have h8 : 0 < 1 + b * c := by nlinarith 
      apply (le_div_iff₀ h8).mpr 
      nlinarith [sq_nonneg (b*c - 1), h, sq_nonneg (a-c), sq_nonneg (b-c), mul_pos hb hc, sq_nonneg (a-b), sq_nonneg (a*c - b*c), sq_nonneg (a*c - a*b), sq_nonneg (b*c - a*b)]
    have h8 : 1 / (1 + c * a) ≥ (3 - c*a) / 4 := by
      have h9 : 0 < 1 + c * a := by nlinarith 
      apply (le_div_iff₀ h9).mpr 
      nlinarith [sq_nonneg (c*a - 1), h, sq_nonneg (a-c), sq_nonneg (b-c), mul_pos hc ha, sq_nonneg (a-b), sq_nonneg (a*c - b*c), sq_nonneg (a*c - a*b), sq_nonneg (b*c - a*b)]
    have h9 : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) ≥ (9 - (a*b + b*c + c*a)) / 4 := by 
      linarith [h6, h7, h8]
    have hab2 : a*b+b*c+c*a ≤ 3 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h10 : (9 - (a*b + b*c + c*a)) / 4 ≥ (9 - 3) / 4 := by 
      have h11 : a*b+b*c+c*a ≤ 3 := hab2
      linarith
    -- Show that (9 - 3) / 4 = 3 / 2
    have h11 : (9 - (a*b + b*c + c*a)) / 4 ≥ 3 / 2 := by 
      nlinarith [h10]
    linarith [h9, h11]
  linarith [h4]
  all_goals try positivity