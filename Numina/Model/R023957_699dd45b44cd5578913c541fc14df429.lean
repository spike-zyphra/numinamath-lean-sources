import Mathlib

theorem algebra_2861 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
(h1 : 8 < a ∧ a < b ∧ b < c) (h2 : 9 < a ∧ a < c ∧ c < b) (h3 : 10 < a ∧ a < d ∧ d < b ∧ d < c) (h4 : 12 < d ∧ d < b ∧ b < c) (h5 : 2 < d ∧ d < c ∧ c < b) : 10 + (c - b) / (a - c) = 10 + (40 / 60) := by
  linarith