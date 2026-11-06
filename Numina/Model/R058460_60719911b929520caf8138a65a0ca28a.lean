import Mathlib

theorem algebra_324416 {x a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    (x + a) * (x + b) / ((c - a) * (c - b)) + (x + b) * (x + c) / ((a - b) * (a - c)) +
    (x + c) * (x + a) / ((b - c) * (b - a)) = 1 := by

  have h1 : a - b ≠ 0 := sub_ne_zero_of_ne ha
  have h2 : b - c ≠ 0 := sub_ne_zero_of_ne hb
  have h3 : a - c ≠ 0 := sub_ne_zero_of_ne hc
  have h4 : c - a ≠ 0 := by
    intro h
    apply hc
    linarith

  have h5 : c - b ≠ 0 := by 
    intro h
    apply hb
    linarith
  
  have h6 : b - a ≠ 0 := by 
    intro h
    apply ha
    linarith
  
  field_simp [h1, h2, h3, h4, h5, h6, show a - b ≠ 0 by exact h1, show b - c ≠ 0 by exact h2, show a - c ≠ 0 by exact h3]
  <;> ring