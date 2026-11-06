import Mathlib

theorem algebra_176883 {a b c : ℝ} (ha : a > b) (h : (a - b) * (b - c) * (c - a) > 0) :
    a > c := by
  have h1 : a - b > 0 := by linarith
  have h2 : (b - c) * (c - a) > 0 := by
    nlinarith [h, h1]
  cases (mul_pos_iff.mp h2) with
  | inl h3 =>
    linarith
  | inr h4 =>
    linarith