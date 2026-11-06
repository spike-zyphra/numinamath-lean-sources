import Mathlib

theorem inequalities_145873 (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (hb : 0 < b)
    (hord : a ≥ b ∧ b ≥ c) (hsum : a + b + c = 3) :
    a * b ^ 2 + b * c ^ 2 + c * a ^ 2 ≤ 27 / 8 := by
  have h1 : a ≥ b := hord.1
  have h2 : b ≥ c := hord.2
  have h3 : a + b + c = 3 := hsum
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
    mul_nonneg (show (0 : ℝ) ≤ a - b by nlinarith) 
      (show (0 : ℝ) ≤ b - c by nlinarith),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
  ]