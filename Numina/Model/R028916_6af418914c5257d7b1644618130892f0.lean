import Mathlib

theorem algebra_154499 {a b : ℝ} (ha : a ≠ -1) (hb : b ≠ -1) (h : a / (1 + b) + b / (1 + a) = 1) :
    a^3 + b^3 = a + b := by
  have h1 : a * (1 + a) + b * (1 + b) = (1 + a) * (1 + b) := by
    have denom_ne_zero : (1 + b) ≠ 0 := by
      intro h3
      apply hb
      linarith
    have denom2_ne_zero : (1 + a) ≠ 0 := by
      intro h3
      apply ha
      linarith
    field_simp [(show 1 + b ≠ 0 by assumption), (show 1 + a ≠ 0 by assumption)] at h ⊢
    nlinarith
  have h2 : a^2 - a * b + b^2 = 1 := by
    nlinarith
  have h3 : a^3 + b^3 = (a + b) * (a^2 - a * b + b^2) := by
    ring
  rw [h3, h2]
  all_goals
    ring
    <;> nlinarith