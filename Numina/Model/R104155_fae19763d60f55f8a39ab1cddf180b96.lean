import Mathlib

theorem algebra_7152 {a b : ℝ} (ha : a ≠ -b) :
    (a + b) / (a + b + 1) = 1 / (1 + 1 / (a + b)) := by 
  have h1 : a + b ≠ 0 := by 
    intro h
    apply ha
    linarith
  field_simp [(show a + b ≠ 0 by exact h1)]
  <;> ring