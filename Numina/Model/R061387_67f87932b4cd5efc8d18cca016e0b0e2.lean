import Mathlib

theorem algebra_77169 {a b c : ℝ} (h : (2 * b - a) ^ 2 + (2 * b - c) ^ 2 = 2 * (2 * b ^ 2 - a * c)) :
    ∃ d, b = a + d ∧ c = b + d := by
  have h1 : (a + c - 2 * b) ^ 2 = 0 := by
    ring_nf at h
    ring_nf
    linarith
  have h2 : a + c - 2 * b = 0 := by 
    apply pow_eq_zero 
    exact h1
  use b - a
  constructor
  . -- Show $b = a + d$
    linarith
  . -- Show $c = b + d$
    linarith [h2]