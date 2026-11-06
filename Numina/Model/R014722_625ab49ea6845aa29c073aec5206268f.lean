import Mathlib

theorem algebra_166609 (x y : ℝ) (hx : x^2 - 3 * y - 88 ≥ 0) (hy : x + 6 * y ≥ 0)
    (h1 : 5 * Real.sqrt (x^2 - 3 * y - 88) + Real.sqrt (x + 6 * y) = 19)
    (h2 : 3 * Real.sqrt (x^2 - 3 * y - 88) = 1 + 2 * Real.sqrt (x + 6 * y)) :
    (x = 10 ∧ y = 1) ∨ (x = -21 / 2 ∧ y = 53 / 12) := by

  have eq1 : 5 * Real.sqrt (x^2 - 3 * y - 88) + Real.sqrt (x + 6 * y) = 19 := h1
  have eq2 : 3 * Real.sqrt (x^2 - 3 * y - 88) = 1 + 2 * Real.sqrt (x + 6 * y) := h2

  have ha : Real.sqrt (x^2 - 3 * y - 88) = 3 := by
    nlinarith [Real.sqrt_nonneg (x^2 - 3 * y - 88), Real.sqrt_nonneg (x + 6 * y),
      sq_nonneg (Real.sqrt (x^2 - 3 * y - 88) - 3), sq_nonneg (Real.sqrt (x + 6 * y) - 4),
      Real.sq_sqrt (show (0 : ℝ) ≤ x^2 - 3 * y - 88 by linarith),
      Real.sq_sqrt (show (0 : ℝ) ≤ x + 6 * y by linarith)]

  have eq3 : x^2 - 3 * y - 88 = 9 := by
    calc
      x^2 - 3 * y - 88 = (Real.sqrt (x^2 - 3 * y - 88)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = 3 ^ 2 := by
        rw [ha]
      _ = (9 : ℝ) := by norm_num

  have hb : Real.sqrt (x + 6 * y) = 4 := by
    nlinarith [Real.sqrt_nonneg (x^2 - 3 * y - 88), Real.sqrt_nonneg (x + 6 * y),
      sq_nonneg (Real.sqrt (x^2 - 3 * y - 88) - 3), sq_nonneg (Real.sqrt (x + 6 * y) - 4),
      Real.sq_sqrt (show (0 : ℝ) ≤ x^2 - 3 * y - 88 by linarith),
      Real.sq_sqrt (show (0 : ℝ) ≤ x + 6 * y by linarith)]

  have eq4 : x + 6 * y = 16 := by
    calc
      x + 6 * y = (Real.sqrt (x + 6 * y)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = 4 ^ 2 := by
        rw [hb]
      _ = (16 : ℝ) := by norm_num

  have eq5 : x^2 - 3 * y = 97 := by 
    linarith

  have eq6 : x + 6 * y = 16 := by
    linarith

  have h3 : (y - 1) * (y - 53 / 12) = 0 := by
    have eq7 : x = 16 - 6 * y := by 
      linarith
    rw [eq7] at eq5
    nlinarith

  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- y = 1
    left
    have eq8 : y = 1 := by linarith
    have eq9 : x = 10 := by 
      nlinarith [eq8, eq6]
    exact ⟨eq9, eq8⟩
  · -- y = 53/12
    right
    have eq8 : y = 53 / 12 := by linarith
    have eq9 : x = -21 / 2 := by 
      nlinarith [eq8, eq6]
    exact ⟨eq9, eq8⟩