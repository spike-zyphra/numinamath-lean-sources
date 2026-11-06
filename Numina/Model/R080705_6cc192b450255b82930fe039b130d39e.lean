import Mathlib

theorem algebra_655 (a b c d : ℝ)
    (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1)
    (hc : 0 < c ∧ c ≠ 1) (hd : 0 < d ∧ d ≠ 1)
    (h1 : 1 / a + 1 / b = 1 / 9) (h2 : 1 / c + 1 / d = 1 / 9 + 1)
    (h3 : 1 / a + 1 / c = 1 / 9 + 1) (h4 : 1 / b + 1 / d = 1 / 9 + 1) :
    1 / a + 1 / b + 1 / c + 1 / d = 1 / 9 + 108 / 60 := by
  linarith