import Mathlib

theorem algebra_327706 {a b : ℝ} (ha : a ≠ -1) (hb : b ≠ -1)
    (hab : a * b = 1) :
    (1 / (1 + a) + 1 / (1 + b)) = (a / (1 + a) + b / (1 + b)) := by
  have h1 : 1 + a ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2 : 1 + b ≠ 0 := by
    intro h
    apply hb
    linarith
  field_simp [(show 1 + a ≠ 0 by assumption), (show 1 + b ≠ 0 by assumption)]
  <;> nlinarith [hab]