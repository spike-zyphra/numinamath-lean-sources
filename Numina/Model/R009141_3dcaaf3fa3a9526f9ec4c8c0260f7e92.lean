import Mathlib

theorem algebra_12959 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a^2 + b^2 + c^2 = 39) (h2 : a * b + b * c + c * a = 21) :
    a + b + c = 9 := by
  have h3 : (a + b + c) ^ 2 = 81 := by
    nlinarith
  have h4 : a + b + c ≥ 0 := by
    linarith
  nlinarith