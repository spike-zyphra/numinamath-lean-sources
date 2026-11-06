import Mathlib

theorem algebra_2558 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    b / ((a - b) * (b - c)) + c / ((b - c) * (c - a)) +
    a / ((c - a) * (a - b)) = 0 := by
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2 : b - c ≠ 0 := by
    intro h
    apply hb
    linarith
  have h3 : c - a ≠ 0 := by
    intro h
    apply hc
    linarith
  field_simp [(show a - b ≠ 0 by assumption), (show b - c ≠ 0 by assumption), (show c - a ≠ 0 by assumption),
  show c - a ≠ 0 by assumption, show a - b ≠ 0 by assumption, show b - c ≠ 0 by assumption]
  ring