import Mathlib

theorem algebra_13233 {x : ℝ} (hx : 0 ≤ x) (h : Real.sqrt (2 + Real.sqrt x) = 3) :
    x = 49 := by

  have h1 : 2 + Real.sqrt x = 9 := by
    calc
      2 + Real.sqrt x = (Real.sqrt (2 + Real.sqrt x)) ^ 2 := by
        rw [Real.sq_sqrt]
        have h2 : 0 ≤ 2 + Real.sqrt x := by
          have h3 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
          linarith
        linarith
      _ = 3 ^ 2 := by rw [h]
      _ = 9 := by norm_num

  have h4 : Real.sqrt x = 7 := by 
    linarith

  have h5 : x = 49 := by 
    calc 
      x = (Real.sqrt x) ^ 2 := by 
        rw [Real.sq_sqrt]
        all_goals linarith 
      _ = 7 ^ 2 := by 
        rw [h4]
      _ = 49 := by 
        norm_num

  exact h5