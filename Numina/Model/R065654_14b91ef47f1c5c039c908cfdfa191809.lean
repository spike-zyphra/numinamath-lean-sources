import Mathlib

theorem algebra_322396 (a x : ℝ) (ha : -1 < a ∧ a < 0) (h : abs (x - a) = a ^ 2) :
    -2 < x ∧ x < 0 := by
  have h1 : -1 < a := ha.1
  have h2 : a < 0 := ha.2
  cases eq_or_eq_neg_of_abs_eq h with
  | inl h3 =>
    -- Case 1: $x - a = a^2$, so $x = a^2 + a$
    have hx1 : x = a ^ 2 + a := by linarith
    constructor
    · -- Show that -2 < x
      rw [hx1]
      nlinarith [sq_nonneg (a + 1 / 2)]
    · -- Show that x < 0
      rw [hx1]
      nlinarith
  | inr h4 =>
    -- Case 2: $x - a = -a^2$, so $x = a - a^2$
    have hx2 : x = a - a ^ 2 := by linarith
    constructor
    · -- Show that -2 < x
      rw [hx2]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (a + 1)]
    · -- Show that x < 0
      rw [hx2]
      nlinarith