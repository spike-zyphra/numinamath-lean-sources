import Mathlib

theorem algebra_252335 {a b c x : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    x^2 = (a^2 * (x - b) * (x - c)) / ((a - b) * (a - c)) +
          (b^2 * (x - a) * (x - c)) / ((b - a) * (b - c)) +
          (c^2 * (x - a) * (x - b)) / ((c - a) * (c - b)) := by
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2 : a - c ≠ 0 := by
    intro h
    apply hc
    linarith
  have h3 : b - a ≠ 0 := by
    intro h
    apply ha
    linarith
  have h4 : b - c ≠ 0 := by
    intro h
    apply hb
    linarith
  have h5 : c - a ≠ 0 := by
    intro h
    apply hc
    linarith
  have h6 : c - b ≠ 0 := by
    intro h
    apply hb
    linarith
  field_simp [(show a - b ≠ 0 by assumption), (show a - c ≠ 0 by assumption), 
              (show b - a ≠ 0 by assumption), (show b - c ≠ 0 by assumption), 
              (show c - a ≠ 0 by assumption), (show c - b ≠ 0 by assumption)]
  ring