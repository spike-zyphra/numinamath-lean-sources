import Mathlib

theorem algebra_98234 (x : ℝ) (hx : 0 ≤ x) (h : Real.sqrt (2 + Real.sqrt x) = 3) : x = 49 := by
  have h1 : 2 + Real.sqrt x = 9 := by
    calc
      2 + Real.sqrt x = (Real.sqrt (2 + Real.sqrt x)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = 3 ^ 2 := by rw [h]
      _ = 9 := by norm_num
  have h2 : Real.sqrt x = 7 := by 
    linarith
  have h3 : x = 49 := by
    calc
      x = (Real.sqrt x) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith
      _ = 7 ^ 2 := by 
        rw [h2]
      _ = 49 := by norm_num
  exact h3