import Mathlib

theorem algebra_204778 {a b c : ℝ} (h : a ≠ -b ∧ b ≠ -c ∧ c ≠ -a) (h' : (a - b) * (b - c) * (c - a) / ((a + b) * (b + c) * (c + a)) = 2004 / 2005) :
    a / (a + b) + b / (b + c) + c / (c + a) = 4011 / 4010 := by

  have h1 : a + b ≠ 0 := by
    intro h2
    apply h.1
    linarith

  have h2 : b + c ≠ 0 := by
    intro h3
    apply h.2.1
    linarith

  have h3 : c + a ≠ 0 := by
    intro h4
    apply h.2.2
    linarith

  have eq1 : (a - b) * (b - c) * (c - a) / ((a + b) * (b + c) * (c + a)) = 2004 / 2005 := h'

  have eq2 : (a - b) * (b - c) * (c - a) = 2004 / 2005 * ((a + b) * (b + c) * (c + a)) := by
    field_simp [show a + b ≠ 0 by exact h1, show b + c ≠ 0 by exact h2, show c + a ≠ 0 by exact h3] at eq1 ⊢
    linarith

  have eq3 : a / (a + b) + b / (b + c) + c / (c + a) = (a * (b + c) * (c + a) + b * (a + b) * (c + a) + c * (a + b) * (b + c)) / ((a + b) * (b + c) * (c + a)) := by
    field_simp [show a + b ≠ 0 by exact h1, show b + c ≠ 0 by exact h2, show c + a ≠ 0 by exact h3]
    ring

  have eq4 : a * (b + c) * (c + a) + b * (a + b) * (c + a) + c * (a + b) * (b + c) = 4011 / 4010 * ((a + b) * (b + c) * (c + a)) := by
    nlinarith [eq2, sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_pos_of_ne_zero (show a + b ≠ 0 by exact h1),
      sq_pos_of_ne_zero (show b + c ≠ 0 by exact h2),
      sq_pos_of_ne_zero (show c + a ≠ 0 by exact h3)]

  rw [eq3]
  field_simp [show a + b ≠ 0 by exact h1, show b + c ≠ 0 by exact h2, show c + a ≠ 0 by exact h3]
  linarith [eq4]