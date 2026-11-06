import Mathlib

theorem algebra_146392 (x : ℝ) (hx : 0 ≤ x) (h : Real.sqrt (2 + Real.sqrt (1 + Real.sqrt (3 * x + 2))) = 2) :
    x = 7 / 3 := by
  have h1 : 2 + Real.sqrt (1 + Real.sqrt (3 * x + 2)) = 4 := by
    calc
      2 + Real.sqrt (1 + Real.sqrt (3 * x + 2)) = (Real.sqrt (2 + Real.sqrt (1 + Real.sqrt (3 * x + 2)))) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = 2 ^ 2 := by rw [h]
      _ = 4 := by norm_num

  have h2 : Real.sqrt (1 + Real.sqrt (3 * x + 2)) = 2 := by linarith

  have h3 : 1 + Real.sqrt (3 * x + 2) = 4 := by
    calc
      1 + Real.sqrt (3 * x + 2) = (Real.sqrt (1 + Real.sqrt (3 * x + 2))) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = 2 ^ 2 := by rw [h2]
      _ = 4 := by norm_num

  have h4 : Real.sqrt (3 * x + 2) = 3 := by linarith

  have h5 : 3 * x + 2 = 9 := by
    calc
      3 * x + 2 = (Real.sqrt (3 * x + 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = 3 ^ 2 := by rw [h4]
      _ = 9 := by norm_num

  linarith