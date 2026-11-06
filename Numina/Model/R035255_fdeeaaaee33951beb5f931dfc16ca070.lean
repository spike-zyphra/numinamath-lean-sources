import Mathlib

theorem algebra_313995 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a > b ∧ b > c) (h2 : 36 - 6 * (a + b + c) + (a * b + b * c + c * a) = 0)
    (h3 : 81 - 9 * (a + b + c) + (a * b + b * c + c * a) = 0) :
    a = 10 ∧ b = 4 ∧ c = 1 := by
  have h5 : (a : ℝ) + (b : ℝ) + (c : ℝ) = 15 := by
    ring_nf at h2 h3
    nlinarith
  have h5_nat : a + b + c = 15 := by exact_mod_cast h5
  have h6 : (a : ℝ) * (b : ℝ) + (b : ℝ) * (c : ℝ) + (c : ℝ) * (a : ℝ) = 54 := by
    ring_nf at h2 h3
    nlinarith
  have h6_nat : a * b + b * c + c * a = 54 := by exact_mod_cast h6
  have h7 : a ≤ 13 := by nlinarith [h5_nat, h6_nat, h1.1, h1.2, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h8 : b ≤ 14 := by nlinarith [h5_nat, h6_nat, h1.1, h1.2, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h9 : c ≤ 14 := by nlinarith [h5_nat, h6_nat, h1.1, h1.2, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  interval_cases a <;> interval_cases b <;> omega