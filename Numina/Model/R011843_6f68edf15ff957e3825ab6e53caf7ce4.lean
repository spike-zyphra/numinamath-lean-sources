import Mathlib

theorem inequalities_154168 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcd : c + d ≤ a ∧ c + d ≤ b) : a * d + b * c ≤ a * b := by 
  have h1 : c + d ≤ a := hcd.1
  have h2 : c + d ≤ b := hcd.2 
  have h3 : 0 ≤ a * b := mul_nonneg ha hb

  by_cases h : a ≤ b 
  · -- Assume a ≤ b 
    have h6 : a * d ≤ a * (a - c) := by 
      have ha_pos : 0 ≤ a := ha 
      have h7 : d ≤ a - c := by linarith 
      nlinarith 
    have h8 : a * (a - c) + b * c ≤ a * b := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (c), sq_nonneg (a - c), mul_nonneg ha hb, mul_nonneg ha hc]

    linarith [h6, h8] 
  · -- Assume b < a 
    have h8 : a * d ≤ a * (b - c) := by 
      have ha_pos : 0 ≤ a := ha 
      have h7 : d ≤ b - c := by linarith 
      nlinarith 
    have h9 : a * (b - c) + b * c ≤ a * b := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (c), sq_nonneg (a - c), mul_nonneg ha hb, mul_nonneg ha hc]

    linarith [h8, h9]