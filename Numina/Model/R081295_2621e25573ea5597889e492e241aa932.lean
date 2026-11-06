import Mathlib

theorem algebra_97776 {a b c : ℝ} (ha : a ≠ 3) (hb : b ≠ 4) (hc : c ≠ 5) :
((a - 3) / (5 - c)) * ((b - 4) / (3 - a)) * ((c - 5) / (4 - b)) = -1 := by
  have h1 : 5 - c ≠ 0 := by
    intro h
    apply hc
    linarith
  have h2 : 3 - a ≠ 0 := by
    intro h
    apply ha
    linarith
  have h3 : 4 - b ≠ 0 := by
    intro h
    apply hb
    linarith
  field_simp [h1, h2, h3]
  <;> ring