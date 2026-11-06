import Mathlib

theorem algebra_301598 (a b : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (h : 20 * a + 30 * b + 70 * (1 - a - b) = 200) :
    a = 0.15 ∧ b = 0.25 := by
  have h1 : a > 0 := ha.1
  have h2 : a < 1 := ha.2
  have h3 : b > 0 := hb.1
  have h4 : b < 1 := hb.2

  -- Rearrange the equation to derive inconsistency
  nlinarith