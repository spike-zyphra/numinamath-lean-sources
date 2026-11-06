import Mathlib

theorem algebra_9121 (x : ℝ) : x ^ 3 = -8 ↔ x = -2 := by
  constructor
  · -- Forward direction: if $x^3 = -8$, then $x = -2$
    intro h
    have h1 : x ^ 3 + 8 = 0 := by linarith
    have h2 : (x + 2) * (x ^ 2 - 2 * x + 4) = 0 := by
      have h_expansion : (x + 2) * (x ^ 2 - 2 * x + 4) = x ^ 3 + 8 := by ring
      linarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where $x + 2 = 0$ (i.e., $x = -2$)
      linarith
    · -- Case where $x^2 - 2x + 4 = 0$
      have h5 : x ^ 2 - 2 * x + 4 > 0 := by
        have h_quadratic_pos : x ^ 2 - 2 * x + 4 = (x - 1) ^ 2 + 3 := by ring
        rw [h_quadratic_pos]
        have h_always_pos : (x - 1) ^ 2 ≥ 0 := by apply sq_nonneg
        linarith
      linarith
  · -- Reverse direction: if $x = -2$, then $x^3 = -8$
    intro h
    rw [h]
    norm_num