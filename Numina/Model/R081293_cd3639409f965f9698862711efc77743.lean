import Mathlib

theorem algebra_223063 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hord : a > b ∧ b > c ∧ c > d) (hprop : a / b = c / d) :
    a + d > b + c := by
  have h1 : a * d = b * c := by
    field_simp [(show b ≠ 0 by linarith), (show d ≠ 0 by linarith)] at hprop
    linarith
  have h4 : (a - c) * (a - b) > 0 := by
    have h5 : a > b := hord.1
    have h6 : b > c := hord.2.1
    have h7 : a > c := by linarith
    have h8 : a - c > 0 := by linarith
    have h9 : a - b > 0 := by linarith
    nlinarith
  have h10 : a * (a + d - (b + c)) > 0 := by
    nlinarith [h1, h4, ha]
  have h11 : a + d - (b + c) > 0 := by
    nlinarith [h10, ha]
  linarith