import Mathlib

theorem algebra_115779 (x y z : ℝ) (hx : x ≥ 4) (hy : y ≥ 9) (hz : z ≥ 22)
    (h : x + y + z - 21 = 2 * Real.sqrt (x - 4) + 4 * Real.sqrt (y - 9) + 6 * Real.sqrt (z - 22)) :
    x = 5 ∧ y = 13 ∧ z = 31 := by

  have h1 : Real.sqrt (x - 4) ≥ 0 := by positivity
  have h2 : Real.sqrt (y - 9) ≥ 0 := by positivity
  have h3 : Real.sqrt (z - 22) ≥ 0 := by positivity
  have eq1 : (Real.sqrt (x - 4)) ^ 2 = x - 4 := by
    rw [Real.sq_sqrt]
    linarith
  have eq2 : (Real.sqrt (y - 9)) ^ 2 = y - 9 := by
    rw [Real.sq_sqrt]
    linarith
  have eq3 : (Real.sqrt (z - 22)) ^ 2 = z - 22 := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : (Real.sqrt (x - 4) - 1) ^ 2 + (Real.sqrt (y - 9) - 2) ^ 2 + (Real.sqrt (z - 22) - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (x - 4) - 1), sq_nonneg (Real.sqrt (y - 9) - 2), sq_nonneg (Real.sqrt (z - 22) - 3), Real.sqrt_nonneg (x - 4), Real.sqrt_nonneg (y - 9), Real.sqrt_nonneg (z - 22), h, eq1, eq2, eq3]
  have h5 : Real.sqrt (x - 4) - 1 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (x - 4) - 1), sq_nonneg (Real.sqrt (y - 9) - 2), sq_nonneg (Real.sqrt (z - 22) - 3), h4]
  have h6 : Real.sqrt (y - 9) - 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (x - 4) - 1), sq_nonneg (Real.sqrt (y - 9) - 2), sq_nonneg (Real.sqrt (z - 22) - 3), h4]
  have h7 : Real.sqrt (z - 22) - 3 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (x - 4) - 1), sq_nonneg (Real.sqrt (y - 9) - 2), sq_nonneg (Real.sqrt (z - 22) - 3), h4]
  have ha1 : Real.sqrt (x - 4) = 1 := by linarith [h5]
  have hb1 : Real.sqrt (y - 9) = 2 := by linarith [h6]
  have hc1 : Real.sqrt (z - 22) = 3 := by linarith [h7]
  have eq21 : x - 4 = 1 := by
    calc
      x - 4 = (Real.sqrt (x - 4)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = (1 : ℝ) ^ 2 := by
        rw [ha1]
      _ = 1 := by
        norm_num
  have eq21' : x = 5 := by linarith [eq21]
  -- y
  have eq22 : y - 9 = 4 := by
    calc
      y - 9 = (Real.sqrt (y - 9)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = (2 : ℝ) ^ 2 := by
        rw [hb1]
      _ = 4 := by
        norm_num
  have eq22' : y = 13 := by linarith [eq22]
  -- z
  have eq23 : z - 22 = 9 := by
    calc
      z - 22 = (Real.sqrt (z - 22)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = (3 : ℝ) ^ 2 := by
        rw [hc1]
      _ = 9 := by
        norm_num
  have eq23' : z = 31 := by linarith [eq23]
  -- Final results
  exact ⟨eq21', eq22', eq23'⟩