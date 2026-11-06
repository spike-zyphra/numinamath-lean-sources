import Mathlib

theorem algebra_234231 {f : ℝ → ℝ} (h : ∀ x, 2 * f x + f (x ^ 2 - 1) = 1) :
    f (Real.sqrt 2) = 1 / 3 := by

  have eq1 := h (Real.sqrt 2)
  have eq2 := h 1
  have eq3 := h (0 : ℝ)
  have eq4 := h (-1 : ℝ)

  have eq5 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  have eq6 : (Real.sqrt 2 : ℝ) ^ 2 - (1 : ℝ) = (1 : ℝ) := by
    linarith [eq5]

  have eq7 : 2 * f (Real.sqrt 2) + f 1 = 1 := by
    rw [eq6] at eq1
    linarith

  have eq8 : 2 * f 1 + f 0 = 1 := by 
    have eq9 : (1 : ℝ) ^ 2 - (1 : ℝ) = (0 : ℝ) := by norm_num
    rw [eq9] at eq2
    linarith

  have eq10 : 2 * f (0 : ℝ) + f (-1 : ℝ) = 1 := by
    have eq11 : (0 : ℝ) ^ 2 - (1 : ℝ) = (-1 : ℝ) := by norm_num
    rw [eq11] at eq3
    linarith

  have eq12 : 2 * f (-1 : ℝ) + f (0 : ℝ) = 1 := by
    have eq13 : (-1 : ℝ) ^ 2 - (1 : ℝ) = (0 : ℝ) := by norm_num
    rw [eq13] at eq4
    linarith

  have eq13 : f 0 = 1 / 3 := by 
    linarith [eq10, eq12]

  have eq14 : f 1 = 1 / 3 := by 
    linarith [eq8, eq13]

  linarith [eq7, eq14]