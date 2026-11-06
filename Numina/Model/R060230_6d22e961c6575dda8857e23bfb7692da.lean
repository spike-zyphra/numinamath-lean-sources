import Mathlib

theorem algebra_297931 (a b c x : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    x^2 = a^2 * (x - b) * (x - c) / ((a - b) * (a - c)) + b^2 * (x - c) * (x - a) / ((b - c) * (b - a)) +
    c^2 * (x - a) * (x - b) / ((c - a) * (c - b)) := by
  have h1 : a - b ≠ 0 := sub_ne_zero.mpr ha
  have h2 : b - c ≠ 0 := sub_ne_zero.mpr hb
  have h3 : a - c ≠ 0 := by 
    intro h
    apply hc
    linarith 
  have h4 : b - a ≠ 0 := by 
    intro h
    apply ha
    linarith 
  have h5 : c - a ≠ 0 := by 
    intro h
    apply hc
    linarith 
  have h6 : c - b ≠ 0 := by 
    intro h
    apply hb
    linarith 
  field_simp [h1, h2, h3, h4, h5, h6]
  ring