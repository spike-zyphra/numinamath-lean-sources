import Mathlib

theorem algebra_100260 (a b c : ℝ) (h : ∀ x, x^2 + 3 * x - 1 = 0 → x^4 + a * x^2 + b * x + c = 0) :
    a + b + 4 * c + 100 = 93 := by

  have eq1 := h ((-3 + Real.sqrt 13) / 2) (by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  )
  have eq2 := h ((-3 - Real.sqrt 13) / 2) (by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  )

  have h1 : ((-3 + Real.sqrt 13) / 2) ^ 2 = -3 * ((-3 + Real.sqrt 13) / 2) + 1 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]

  have h2 : ((-3 - Real.sqrt 13) / 2) ^ 2 = -3 * ((-3 - Real.sqrt 13) / 2) + 1 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]

  have eq1' : ((-3 + Real.sqrt 13) / 2) ^ 4 = -33 * ((-3 + Real.sqrt 13) / 2) + 10 := by
    calc
      ((-3 + Real.sqrt 13) / 2) ^ 4 = (((-3 + Real.sqrt 13) / 2) ^ 2) ^ 2 := by ring
      _ = (-3 * ((-3 + Real.sqrt 13) / 2) + 1) ^ 2 := by rw [h1]
      _ = 9 * ((-3 + Real.sqrt 13) / 2) ^ 2 - 6 * ((-3 + Real.sqrt 13) / 2) + 1 := by ring
      _ = 9 * (-3 * ((-3 + Real.sqrt 13) / 2) + 1) - 6 * ((-3 + Real.sqrt 13) / 2) + 1 := by 
        rw [h1]
      _ = -33 * ((-3 + Real.sqrt 13) / 2) + 10 := by 
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13)]

  have eq2' : ((-3 - Real.sqrt 13) / 2) ^ 4 = -33 * ((-3 - Real.sqrt 13) / 2) + 10 := by 
    calc
      ((-3 - Real.sqrt 13) / 2) ^ 4 = (((-3 - Real.sqrt 13) / 2) ^ 2) ^ 2 := by ring
      _ = (-3 * ((-3 - Real.sqrt 13) / 2) + 1) ^ 2 := by
        rw [h2]
      _ = 9 * ((-3 - Real.sqrt 13) / 2) ^ 2 - 6 * ((-3 - Real.sqrt 13) / 2) + 1 := by 
        ring
      _ = 9 * (-3 * ((-3 - Real.sqrt 13) / 2) + 1) - 6 * ((-3 - Real.sqrt 13) / 2) + 1 := by 
        rw [h2]
      _ = -33 * ((-3 - Real.sqrt 13) / 2) + 10 := by 
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13)]

  rw [eq1'] at eq1
  rw [eq2'] at eq2

  rw [show ((-3 + Real.sqrt 13) / 2) ^ 2 = -3 * ((-3 + Real.sqrt 13) / 2) + 1 by linarith [h1] ] at eq1 
  rw [show ((-3 - Real.sqrt 13) / 2) ^ 2 = -3 * ((-3 - Real.sqrt 13) / 2) + 1 by linarith [h2] ] at eq2

  have eq3 : (-33 - 3 * a + b) * ((-3 + Real.sqrt 13) / 2) + (10 + a + c) = 0 := by
    nlinarith 
  have eq4 : (-33 - 3 * a + b) * ((-3 - Real.sqrt 13) / 2) + (10 + a + c) = 0 := by 
    nlinarith

  have eq5 : -33 - 3 * a + b = 0 := by
    have eq8 : ((-3 + Real.sqrt 13) / 2) ≠ ((-3 - Real.sqrt 13) / 2) := by
      by_contra h
      have h9 : Real.sqrt 13 = 0 := by
        nlinarith [h, Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num)]
      have h10 : Real.sqrt 13 > 0 := Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num)
      linarith [h9, h10]
    have eq9 : (-33 - 3 * a + b) * ((-3 + Real.sqrt 13) / 2) = (-33 - 3 * a + b) * ((-3 - Real.sqrt 13) / 2) := by
      linarith [eq3, eq4]
    have eq10 : (-33 - 3 * a + b) * (Real.sqrt 13) = 0 := by
      have h11 : ((-3 + Real.sqrt 13) / 2) - ((-3 - Real.sqrt 13) / 2) = Real.sqrt 13 := by 
        linarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num)]
      have eq11 : (-33 - 3 * a + b) * ((-3 + Real.sqrt 13) / 2) - (-33 - 3 * a + b) * ((-3 - Real.sqrt 13) / 2) = 0 := by linarith [eq9]
      have eq12 : (-33 - 3 * a + b) * ((-3 + Real.sqrt 13) / 2 - ((-3 - Real.sqrt 13) / 2)) = 0 := by 
        linarith [eq11]
      rw [show ((-3 + Real.sqrt 13) / 2 - ((-3 - Real.sqrt 13) / 2)) = Real.sqrt 13 by linarith] at eq12
      linarith
    have h12 : Real.sqrt 13 ≠ 0 := by
      positivity
    have eq13 : -33 - 3 * a + b = 0 := by 
      apply (mul_left_inj' h12).mp
      linarith 
    linarith

  have eq6 : b = 33 + 3 * a := by 
    linarith 
  have eq7 : 10 + a + c = 0 := by
    have h3 : ((-3 + Real.sqrt 13) / 2) + ((-3 - Real.sqrt 13) / 2) = -3 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13)]
    nlinarith [eq3, eq4, eq5, h3, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  have eq8 : c = -10 - a := by 
    linarith 
  linarith [eq6, eq8]