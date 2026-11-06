import Mathlib

theorem algebra_15798 {x : ℝ} (hx : 0 < x ∧ x < 1) (h : (Real.logb 10 x)^2 - Real.logb 10 (x^2) = 48) :
    (Real.logb 10 x)^3 - Real.logb 10 (x^3) = -198 := by
  have h1 : Real.logb 10 (x^2) = 2 * Real.logb 10 x := by
    simp [Real.logb_pow]

  have h2 : Real.logb 10 (x^3) = 3 * Real.logb 10 x := by
    simp [Real.logb_pow]

  rw [h1] at h
  rw [h2]

  have h3 : 0 < x := hx.1
  have h4 : x < 1 := hx.2

  have h5 : (Real.logb 10 x) ^ 2 - 2 * (Real.logb 10 x) - 48 = 0 := by 
    linarith

  -- Factorizing the quadratic equation
  have h6 : (Real.logb 10 x - 8) * (Real.logb 10 x + 6) = 0 := by
    nlinarith
  
  rcases (mul_eq_zero.1 h6) with h7 | h8
  · -- Real.logb 10 x = 8
    have h8' : Real.logb 10 x = 8 := by linarith
    -- This is a contradiction because x < 1 implies logb 10 x < 0
    have h9 : Real.logb 10 x < 0 := by
      have h10 : Real.logb 10 x < Real.logb 10 1 := by 
        apply Real.logb_lt_logb
        all_goals
          try linarith
      have h11 : Real.logb 10 1 = 0 := Real.logb_one
      linarith [h10, h11]
    linarith

  · -- Real.logb 10 x = -6
    have h9 : Real.logb 10 x = -6 := by linarith
    rw [h9]
    norm_num