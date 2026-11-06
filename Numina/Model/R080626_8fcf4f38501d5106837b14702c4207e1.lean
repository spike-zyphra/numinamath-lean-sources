import Mathlib

theorem algebra_328179 {a b c : ℝ} (ha : a ≠ b) (hb : a ≠ c) (hc : b ≠ c) :
    (2 * a - b - c) / ((a - b) * (a - c)) + (2 * b - c - a) / ((b - c) * (b - a)) +
    (2 * c - a - b) / ((c - a) * (c - b)) = 0 := by
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2 : a - c ≠ 0 := by
    intro h
    apply hb
    linarith
  have h3 : b - c ≠ 0 := by
    intro h
    apply hc
    linarith
  have h4 : b - a ≠ 0 := by
    intro h
    apply ha
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