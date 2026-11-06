import Mathlib

theorem inequalities_276959 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b + b * c + a * c ≤ 3 * a * b * c := by
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b * c by nlinarith), mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ a * c by nlinarith), mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a * b by nlinarith)]