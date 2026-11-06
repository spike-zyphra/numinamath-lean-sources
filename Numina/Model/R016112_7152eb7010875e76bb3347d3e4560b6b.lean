import Mathlib

theorem algebra_313623 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : a + b = 2) (h2 : (1 - a)^2 / b + (1 - b)^2 / a = -4) :
    a * b = -1 := by
  have h3 : a * (1 - a) ^ 2 + b * (1 - b) ^ 2 = -4 * (a * b) := by
    have hne : a ≠ 0 := ha
    have hne2 : b ≠ 0 := hb
    field_simp [ha, hb] at h2 ⊢
    linarith
  have hb_eq : b = 2 - a := by linarith
  rw [hb_eq] at h3
  -- Now we have the equation clear denominators, so we have a polynomial equation.
  have h4 : a * (1 - a) ^ 2 + (2 - a) * (1 - (2 - a)) ^ 2 = -4 * (a * (2 - a)) := by linarith [h3]
  have h6 : a ^ 2 - 2 * a - 1 = 0 := by
    nlinarith
  have h8 : a * b = -1 := by
    rw [show b = 2 - a by linarith]
    nlinarith [ sq_nonneg (a - (2 - a)), sq_nonneg (a + (2 - a) - 2), sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show (2 - a) ≠ 0 by 
      intro h
      apply hb
      linarith
    ) ]
  exact h8