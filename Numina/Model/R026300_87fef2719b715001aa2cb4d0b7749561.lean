import Mathlib

theorem algebra_309339 {x y : ℝ} (h : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = 1) : x + y = 0 := by

  have h1 : x + Real.sqrt (x^2 + 1) ≠ 0 := by 
    by_contra h1 
    have h2 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = 0 := by 
      rw [h1]
      all_goals 
        norm_num
    nlinarith 

  have h22 : y + Real.sqrt (y^2 + 1) ≠ 0 := by 
    by_contra h22 
    have h33 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = 0 := by 
      rw [h22]
      all_goals 
        norm_num 
    nlinarith

  have eq1 : x - Real.sqrt (x^2 + 1) = - (y + Real.sqrt (y^2 + 1)) := by 
    have h3 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = 1 := h
    have eq2 : (x + Real.sqrt (x^2 + 1)) * (x - Real.sqrt (x^2 + 1)) = -1 := by
      have h4 : (Real.sqrt (x^2 + 1)) ^ 2 = x^2 + 1 := Real.sq_sqrt (show x^2 + 1 ≥ 0 by nlinarith)
      nlinarith [Real.sqrt_nonneg (x^2 + 1)]
    have eq7 : (x - Real.sqrt (x^2 + 1)) + (y + Real.sqrt (y^2 + 1)) = 0 := by
      have eq8 : (x + Real.sqrt (x^2 + 1)) * ((x - Real.sqrt (x^2 + 1)) + (y + Real.sqrt (y^2 + 1))) = 0 := by
        nlinarith 
      cases (mul_eq_zero.mp eq8) with
      | inl h9 => 
        contradiction 
      | inr h10 => 
        linarith 
    linarith

  have eq8 : y - Real.sqrt (y^2 + 1) = - (x + Real.sqrt (x^2 + 1)) := by 
    have h3 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = 1 := h
    have eq2 : (y + Real.sqrt (y^2 + 1)) * (y - Real.sqrt (y^2 + 1)) = -1 := by 
      have h4 : (Real.sqrt (y^2 + 1)) ^ 2 = y^2 + 1 := Real.sq_sqrt (show y^2 + 1 ≥ 0 by nlinarith)
      nlinarith [Real.sqrt_nonneg (y^2 + 1)]
    have eq7 : (y - Real.sqrt (y^2 + 1)) + (x + Real.sqrt (x^2 + 1)) = 0 := by
      have eq8 : (y + Real.sqrt (y^2 + 1)) * ((y - Real.sqrt (y^2 + 1)) + (x + Real.sqrt (x^2 + 1))) = 0 := by
        nlinarith 
      cases (mul_eq_zero.mp eq8) with
      | inl h9 => 
        contradiction 
      | inr h10 => 
        linarith 
    linarith

  have eq10 : 2 * (x + y) = 0 := by
    nlinarith [eq1, eq8, Real.sqrt_nonneg (x^2 + 1), Real.sqrt_nonneg (y^2 + 1)]

  linarith