import Mathlib

theorem algebra_2863 {x : ℝ} (hx : x ≥ 0) (h : x - 5 * Real.sqrt x - 36 = 0) : x = 81 := by
  have h1 : Real.sqrt x ≥ 0 := by
    apply Real.sqrt_nonneg
  have h2 : (Real.sqrt x) ^2 = x := by
    rw [Real.sq_sqrt]
    linarith
  have h3 : (Real.sqrt x) ^2 - 5 * Real.sqrt x - 36 = 0 := by 
    nlinarith [h, h2]
  have h4 : (Real.sqrt x - 9) * (Real.sqrt x + 4) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case Real.sqrt x - 9 = 0, thus Real.sqrt x = 9
    have h7 : Real.sqrt x = 9 := by linarith
    have h8 : x = 81 := by
      calc
        x = (Real.sqrt x) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = 9 ^ 2 := by 
          rw [h7]
        _ = 81 := by 
          norm_num
    linarith
  · -- Case Real.sqrt x + 4 = 0, thus Real.sqrt x = -4
    have h7 : Real.sqrt x = -4 := by linarith
    nlinarith [h1, h7]