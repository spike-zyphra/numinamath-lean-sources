import Mathlib

theorem algebra_187685 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    1 / ((a - b) * (a - c)) + 1 / ((b - a) * (b - c)) + 1 / ((c - a) * (c - b)) = 0 := by
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2 : b - a ≠ 0 := by
    intro h
    apply ha
    linarith
  have h3 : b - c ≠ 0 := by
    intro h
    apply hb
    linarith
  have h4 : c - a ≠ 0 := by
    intro h
    apply hc
    linarith
  have h5 : c - b ≠ 0 := by
    intro h
    apply hb
    linarith
  have h6 : a - c ≠ 0 := by
    intro h
    apply hc
    linarith
  field_simp [(show (a - b) ≠ 0 by exact h1), (show (a - c) ≠ 0 by exact h6), (show (b - a) ≠ 0 by exact h2), (show (b - c) ≠ 0 by exact h3), (show (c - a) ≠ 0 by exact h4), (show (c - b) ≠ 0 by exact h5)]
  ring