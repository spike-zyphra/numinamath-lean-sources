import Mathlib

theorem algebra_252806 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    b * c / ((a - c) * (a - b)) + a * c / ((b - c) * (b - a)) +
    a * b / ((c - a) * (c - b)) = 1 := by
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2 : b - c ≠ 0 := by
    intro h
    apply hb
    linarith
  have h3 : a - c ≠ 0 := by
    intro h
    apply hc
    linarith
  have h4 : b - a ≠ 0 := by
    intro h
    have h5 : a = b := by linarith
    tauto
  have h5 : c - a ≠ 0 := by
    intro h
    have h6 : a = c := by linarith
    tauto
  have h6 : c - b ≠ 0 := by
    intro h
    have h7 : b = c := by linarith
    tauto
  field_simp [(show a - c ≠ 0 by assumption), (show a - b ≠ 0 by assumption), (show b - c ≠ 0 by assumption), (show b - a ≠ 0 by assumption), (show c - a ≠ 0 by assumption), (show c - b ≠ 0 by assumption)]
  ring