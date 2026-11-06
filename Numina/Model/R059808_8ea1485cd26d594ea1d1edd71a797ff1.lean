import Mathlib

theorem algebra_230589 {a b c : ℝ} (ha : a ≠ b) (hc : a ≠ c) (h : a^2 = b * c) :
    (a + b) / (a - b) = (c + a) / (c - a) := by 
  have h1 : a - b ≠ 0 := by
    intro h2
    apply ha
    linarith

  have h2 : c - a ≠ 0 := by
    intro h3
    apply hc
    linarith

  have eq1 : (a + b) / (a - b) = (c + a) / (c - a) := by 
    field_simp [h1, h2]
    nlinarith [h]

  exact eq1