import Mathlib

theorem algebra_15466 (a b c x : ℝ) (ha : a ≠ b) (hb : a ≠ c) (hc : b ≠ c) :
    ((x + a)^3 / ((a - b) * (a - c)) + (x + b)^3 / ((b - a) * (b - c)) +
     (x + c)^3 / ((c - a) * (c - b))) = a + b + c + 3 * x := by

  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith

  have h2 : a - c ≠ 0 := by
    intro h
    apply hb
    linarith

  have h3 : b - a ≠ 0 := by
    intro h
    apply ha
    linarith

  have h4 : b - c ≠ 0 := by
    intro h
    apply hc
    linarith

  have h5 : c - a ≠ 0 := by
    intro h
    apply hb
    linarith

  have h6 : c - b ≠ 0 := by
    intro h
    apply hc
    linarith

  field_simp [h1, h2, h3, h4, h5, h6]
  ring