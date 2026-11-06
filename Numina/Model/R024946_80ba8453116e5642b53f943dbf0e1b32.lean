import Mathlib

theorem algebra_101247 (a b c : ℝ) (h : ∀ x, x^2 + 3 * x - 1 = 0 → x^4 + a * x^2 + b * x + c = 0) :
    a + b + 4 * c = -7 := by

  have eq1 := h ((-3 + Real.sqrt 13) / 2) (by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
  )

  have eq2 := h ((-3 - Real.sqrt 13) / 2) (by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
  )

  have hr1_sq : ((-3 + Real.sqrt 13) / 2) ^2 = 1 - 3 * ((-3 + Real.sqrt 13) / 2) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]

  have hr1_sq2 : ((-3 + Real.sqrt 13) / 2) ^4 = (10 - 33 * ((-3 + Real.sqrt 13) / 2) ) := by 
    calc
      ((-3 + Real.sqrt 13) / 2) ^4 = (((-3 + Real.sqrt 13) / 2) ^2) ^2 := by ring
      _ = (1 - 3 * ((-3 + Real.sqrt 13) / 2)) ^2 := by rw [hr1_sq]
      _ = (10 - 33 * ((-3 + Real.sqrt 13) / 2) ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]

  have hr2_sq : ((-3 - Real.sqrt 13) / 2) ^2 = 1 - 3 * ((-3 - Real.sqrt 13) / 2) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]

  have hr2_sq2 : ((-3 - Real.sqrt 13) / 2) ^4 = (10 - 33 * ((-3 - Real.sqrt 13) / 2) ) := by 
    calc
      ((-3 - Real.sqrt 13) / 2) ^4 = (((-3 - Real.sqrt 13) / 2) ^2) ^2 := by ring
      _ = (1 - 3 * ((-3 - Real.sqrt 13) / 2)) ^2 := by rw [hr2_sq]
      _ = (10 - 33 * ((-3 - Real.sqrt 13) / 2) ) := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]

  rw [hr1_sq2, hr1_sq] at eq1
  rw [hr2_sq2, hr2_sq] at eq2 
  ring_nf at eq1 eq2
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num), sq_nonneg (Real.sqrt 13)]