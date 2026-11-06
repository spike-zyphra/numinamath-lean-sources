import Mathlib

theorem algebra_8181 {a b : ℝ} (ha : a ≠ b) (hb : b ≠ a) : -a / (-a + b) = a / (a - b) := by
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h3 : -a + b ≠ 0 := by 
    intro h
    apply hb
    linarith
  field_simp [h1, h3]
  <;> ring