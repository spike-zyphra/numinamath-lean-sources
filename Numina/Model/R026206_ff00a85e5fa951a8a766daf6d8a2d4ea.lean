import Mathlib

theorem algebra_322146 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
    ¬∃ x : ℝ, a^2 * x^2 - (c^2 - a^2 - b^2) * x + b^2 = 0 := by
  rintro ⟨x, he⟩
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc
  have h4 : (a + b) ^ 2 > c ^ 2 := by nlinarith
  have h5 : (a - b) ^ 2 < c ^ 2 := by nlinarith
  have h6 : (c ^ 2 - a ^ 2 - b ^ 2) ^ 2 < 4 * a ^ 2 * b ^ 2 := by
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h8 : (c ^ 2 - a^2 - b^2) ^ 2 - 4 * a^2 * b^2 < 0 := by nlinarith [h6]
  have h9 : a ^ 2 ≠ 0 := by nlinarith
  have h10 : (2 * a^2 * x - (c^2 - a^2 - b^2)) ^ 2 = 4 * a^2 * b^2 - (c^2 - a^2 - b^2) ^ 2 := by
    nlinarith
  have h11 : (2 * a^2 * x - (c^2 - a^2 - b^2)) ^ 2 ≥ 0 := by nlinarith [sq_nonneg (2 * a^2 * x - (c^2 - a^2 - b^2))]
  have h12 : 4 * a^2 * b^2 - (c^2 - a^2 - b^2) ^ 2 < 0 := by nlinarith [h8]
  nlinarith
  all_goals nlinarith