import Mathlib

theorem inequalities_63556 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    ((a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3) /
    ((a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3) > 8 * a * b * c := by

  have hab1 : a - b ≠ 0 := by
    intro h1
    apply habc.left
    linarith

  have h1 : b - c ≠ 0 := by
    intro h1
    apply habc.right.left
    linarith

  have h2 : c - a ≠ 0 := by
    intro h1
    apply habc.right.right
    linarith

  have eq1 : ((a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3) =
      3 * ((a ^ 2 - b ^ 2) * (b ^ 2 - c ^ 2) * (c ^ 2 - a ^ 2)) := by
    ring_nf

  have eq2 : ((a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3) =
      3 * ((a - b) * (b - c) * (c - a)) := by
    ring_nf

  have eq3 : ((a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3) / ((a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3) = (a + b) * (b + c) * (c + a) := by
    rw [eq1, eq2]
    field_simp [(show (a - b) ≠ 0 by exact hab1),
      (show (b - c) ≠ 0 by exact h1), (show (c - a) ≠ 0 by exact h2)]
    ring_nf

  rw [eq3] at *
  have h3 : (a + b) * (b + c) * (c + a) > 8 * a * b * c := by
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
      sq_pos_of_ne_zero (show a - b ≠ 0 by exact hab1),
      sq_pos_of_ne_zero (show b - c ≠ 0 by exact h1),
      sq_pos_of_ne_zero (show c - a ≠ 0 by exact h2),
      sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
      mul_pos ha (show b * c > 0 by nlinarith),
      mul_pos hb (show a * c > 0 by nlinarith),
      mul_pos hc (show a * b > 0 by nlinarith),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  linarith [h3]