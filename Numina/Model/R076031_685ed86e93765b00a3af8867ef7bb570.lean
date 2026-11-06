import Mathlib

theorem algebra_237014 (x : ℝ) (hx : x^4 + 2 * x^3 - x^2 - 2 * x - 3 = 0) (h : x^4 + 3 * x^3 + x^2 - 4 * x - 6 = 0) :
    x = (-1 - Real.sqrt 13) / 2 ∨ x = (-1 + Real.sqrt 13) / 2 := by

  -- Subtract the two equations
  have h_sub : x^3 + 2 * x^2 - 2 * x - 3 = 0 := by
    nlinarith

  have h_eq : (x + 1) * (x^2 + x - 3) = 0 := by 
    nlinarith

  cases' (mul_eq_zero.mp h_eq) with h1 h2

  · -- Case where $x + 1 = 0$
    have h11 : x = -1 := by linarith
    rw [h11] at hx h
    norm_num at hx h
    all_goals linarith

  · -- Case where $x^2 + x - 3 = 0$
    have h_eq1 : x^2 + x - 3 = 0 := by
      linarith

    have h_eq3 : (x - (-1 - Real.sqrt 13) / 2) * (x - (-1 + Real.sqrt 13) / 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]

    cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
    · -- Case where $x - (-1 - Real.sqrt 13) / 2 = 0$
      left
      linarith
    · -- Case where $x - (-1 + Real.sqrt 13) / 2 = 0$
      right
      linarith