import Mathlib

theorem algebra_275461 (a : ℝ) (M : Set ℝ) (hM : M = {x | x^2 - 3 * x - a^2 + 2 = 0}) :
    2^M.ncard = 4 := by
  have h3 : M = { (3 + Real.sqrt (4 * a^2 + 1)) / 2, (3 - Real.sqrt (4 * a^2 + 1)) / 2 } := by
    ext x
    simp [hM]
    constructor
    · -- Suppose x is a solution of x^2 - 3 x - a^2 + 2 = 0.
      intro hx
      have h_eq : x^2 - 3 * x - a^2 + 2 = 0 := hx
      have h4 : (x - (3 + Real.sqrt (4 * a^2 + 1)) / 2) * (x - (3 - Real.sqrt (4 * a^2 + 1)) / 2) = 0 := by
        nlinarith [Real.sqrt_nonneg (4 * a^2 + 1), Real.sq_sqrt (show (4 * a^2 + 1) ≥ 0 by nlinarith)]
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- Case where x equals the first root.
        left
        linarith
      · -- Case where x equals the second root.
        right
        linarith
    · -- Show that the two roots satisfy the equation.
      rintro (rfl | rfl)
      · -- Show x^2 -3 x -a^2 +2 =0 for x = (3 + Real.sqrt (4 * a^2 + 1)) / 2
        nlinarith [Real.sqrt_nonneg (4 * a^2 + 1), Real.sq_sqrt (show (4 * a^2 + 1) ≥ 0 by nlinarith)]
      · -- Show x^2 -3 x -a^2 +2 =0 for x = (3 - Real.sqrt (4 * a^2 + 1)) / 2
        nlinarith [Real.sqrt_nonneg (4 * a^2 + 1), Real.sq_sqrt (show (4 * a^2 + 1) ≥ 0 by nlinarith)]

  rw [h3]

  have h4 : Real.sqrt (4 * a^2 + 1) > 0 := by
    have h1 : 4 * a^2 + 1 > 0 := by
      nlinarith [sq_nonneg a]
    have h2 : Real.sqrt (4 * a^2 + 1) > 0 := by
      apply Real.sqrt_pos.2 h1
    linarith

  have h5 : ({ (3 + Real.sqrt (4 * a^2 + 1)) / 2, (3 - Real.sqrt (4 * a^2 + 1)) / 2 } : Set ℝ).ncard = 2 := by
    have h6 : (3 + Real.sqrt (4 * a^2 + 1)) / 2 ≠ (3 - Real.sqrt (4 * a^2 + 1)) / 2 := by
      intro h
      have h1 : Real.sqrt (4 * a^2 + 1) = 0 := by
        linarith [Real.sqrt_nonneg (4 * a^2 + 1)]
      have h2 : Real.sqrt (4 * a^2 + 1) > 0 := h4
      linarith [Real.sqrt_nonneg (4 * a^2 + 1)]
    simp [Set.ncard_pair h6]

  rw [h5]
  norm_num