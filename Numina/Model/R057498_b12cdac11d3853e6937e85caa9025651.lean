import Mathlib

theorem algebra_22109 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (x : ℝ) :
    (x + a)^2 / ((a - b) * (a - c)) + (x + b)^2 / ((b - a) * (b - c)) +
    (x + c)^2 / ((c - a) * (c - b)) = 1 := by 
  have h1 : a - b ≠ 0 := sub_ne_zero_of_ne ha
  have h2 : b - a ≠ 0 := by 
    intro h
    apply ha
    linarith
  have h3 : b - c ≠ 0 := sub_ne_zero_of_ne hb
  have h4 : c - b ≠ 0 := by 
    intro h
    apply hb
    linarith
  have h5 : a - c ≠ 0 := by 
    intro h
    apply hc
    linarith
  have h6 : c - a ≠ 0 := by 
    intro h
    apply hc
    linarith 
  field_simp [h1, h2, h3, h4, h5, h6]
  ring