import Mathlib

theorem algebra_601557 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
    ¬∃ x : ℝ, b^2 * x^2 + (b^2 + c^2 - a^2) * x + c^2 = 0 := by
  rintro ⟨x, hx⟩
  have h2 : (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 - 4 * (b ^ 2) * (c ^ 2) < 0 := by
    have h3 : a ^ 2 < (b + c) ^ 2 := by
      nlinarith [h']
    have h4 : a ^ 2 > (b - c) ^ 2 := by
      nlinarith [h'', sq_nonneg (b - c), sq_nonneg (a), sq_nonneg (b + c - a)]
    nlinarith [h3, h4]
  have h4 : (2 * b^2 * x + (b^2 + c^2 - a^2)) ^ 2 = (b^2 + c^2 - a^2) ^ 2 - 4 * (b^2) * (c^2) := by
    nlinarith [hx]
  have h5 : (2 * b^2 * x + (b^2 + c^2 - a^2)) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  nlinarith [h4, h5, h2]