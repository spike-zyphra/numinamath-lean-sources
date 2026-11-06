import Mathlib

open Real

theorem algebra_187440 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : 1 / 2 * logb 2 x - logb 2 y = 0) (h2 : x ^ 2 - 2 * y ^ 2 = 8) :
    x = 4 ∧ y = 2 := by
  have eq1 : 1 / 2 * logb 2 x = logb 2 y := by linarith 
  have eq2 : 1 / 2 * logb 2 x = logb 2 (Real.sqrt x) := by
    have h3 : Real.sqrt x = (x) ^ (1 / 2 : ℝ) := by 
      rw [Real.sqrt_eq_rpow]
    rw [h3]
    have h4 : logb 2 ((x) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * logb 2 x := by 
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith
    linarith
  rw [eq2] at eq1
  have eq3 : Real.sqrt x = y := by 
    have h5 : logb 2 (Real.sqrt x) = logb 2 y := eq1
    have h6 : Real.sqrt x > 0 := by
      apply Real.sqrt_pos.2
      linarith
    have h7 : y > 0 := hy
    have h8 : Real.sqrt x = y := by
      apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h6) (Set.mem_Ioi.mpr h7) h5
    exact h8
  have eq4 : x = y ^ 2 := by
    calc
      x = (Real.sqrt x) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith
      _ = y ^ 2 := by 
        rw [eq3]
  -- Substitute x = y^2 into the second equation
  have eq5 : (y ^ 2) ^ 2 - 2 * (y ^ 2) = 8 := by
    rw [show x = y ^ 2 by linarith [eq4]] at h2
    nlinarith
  have eq6 : (y ^ 2 - 4) * (y ^ 2 + 2) = 0 := by 
    nlinarith [eq5]
  cases' (mul_eq_zero.1 eq6) with eq7 eq8
  · -- Case $y^2 - 4 = 0$
    have eq8 : y ^ 2 = 4 := by
      linarith
    have hy2 : y = 2 := by 
      nlinarith [sq_pos_of_pos hy]
    have hx4 : x = 4 := by 
      nlinarith [eq4, hy2]
    exact ⟨hx4, hy2⟩
  · -- Case $y^2 + 2 = 0$
    have eq9 : y ^ 2 = -2 := by 
      nlinarith
    nlinarith [sq_pos_of_pos hy, eq9]