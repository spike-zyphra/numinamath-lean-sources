import Mathlib

open Real

theorem algebra_179776 {x : ℝ} (hx : 0 < x) :
    logb 10 (100 * x) ^ 2 + logb 10 (10 * x) ^ 2 = 14 + logb 10 (1 / x) ↔
    x = 10 ^ (-9 / 2 : ℝ) ∨ x = 10 := by
  constructor
  · -- Assume the equation holds, prove the solutions
    intro h
    have h1 : logb 10 (100 * x) = 2 + logb 10 x := by
      calc
        logb 10 (100 * x)
            = logb 10 (100) + logb 10 x := by
              rw [logb_mul (by norm_num) (by linarith)]
            _ = logb 10 (10 ^ (2 : ℝ)) + logb 10 x := by
              norm_num
            _ = 2 + logb 10 x := by
              rw [logb_rpow (by norm_num)]
              all_goals norm_num
    have h2 : logb 10 (10 * x) = 1 + logb 10 x := by
      calc
        logb 10 (10 * x)
            = logb 10 10 + logb 10 x := by
              rw [logb_mul (by norm_num) (by linarith)]
            _ = 1 + logb 10 x := by
              norm_num
    have h3 : logb 10 (1 / x) = - logb 10 x := by
      calc
        logb 10 (1 / x)
            = logb 10 1 - logb 10 x := by
              field_simp [logb_div]
            _ = 0 - logb 10 x := by
              simp
            _ = - logb 10 x := by
              ring
    rw [h1, h2, h3] at h
    have h4 : 2 * (logb 10 x) ^ 2 + 7 * (logb 10 x) - 9 = 0 := by 
      nlinarith
    have h5 : (logb 10 x - 1) * (2 * (logb 10 x) + 9) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- case where logb 10 x - 1 = 0, so logb 10 x = 1
      have h8 : logb 10 x = 1 := by linarith
      have h9 : x = 10 := by
        have h10 : logb 10 x = 1 := h8
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith)] at h10
        · linarith
        all_goals linarith
      right
      exact h9
    · -- case where 2 * logb 10 x + 9 = 0, so logb 10 x = -9/2
      have h10 : logb 10 x = -9 / 2 := by linarith
      have h11 : x = (10 : ℝ) ^ (-9 / 2 : ℝ) := by
        have h12 : logb 10 x = -9 / 2 := h10
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith)] at h12
        · linarith
        all_goals linarith
      left
      exact h11
  · -- Assume the solutions, prove the equation
    rintro (h | h)
    · -- case where x = 10 ^ (-9 / 2)
      rw [h]
      have h1 : logb 10 (100 * ((10 : ℝ) ^ (-9 / 2 : ℝ))) = 2 + logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by
        calc
          logb 10 (100 * ((10 : ℝ) ^ (-9 / 2 : ℝ)))
              = logb 10 (100) + logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by
                rw [logb_mul (by norm_num) (by positivity)]
              _ = logb 10 (10 ^ (2 : ℝ)) + logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by
                norm_num
              _ = 2 + logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by
                rw [logb_rpow (by norm_num)]
                all_goals norm_num
      have h2 : logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) = (-9 / 2 : ℝ) := by 
        rw [logb_rpow (by norm_num)]
        all_goals norm_num
      have h3 : logb 10 (10 * ((10 : ℝ) ^ (-9 / 2 : ℝ))) = 1 + logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by
        calc
          logb 10 (10 * ((10 : ℝ) ^ (-9 / 2 : ℝ)))
              = logb 10 10 + logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by 
                rw [logb_mul (by norm_num) (by positivity)]
              _ = 1 + logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by 
                norm_num
      have h4 : logb 10 (1 / ((10 : ℝ) ^ (-9 / 2 : ℝ)) ) = - logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by 
        calc
          logb 10 (1 / ((10 : ℝ) ^ (-9 / 2 : ℝ)) )
              = logb 10 1 - logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by 
                field_simp [logb_div]
              _ = 0 - logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by 
                simp
              _ = - logb 10 ((10 : ℝ) ^ (-9 / 2 : ℝ)) := by 
                ring
      rw [h1, h3, h4, h2]
      <;> nlinarith
    · -- case where x = 10
      rw [h]
      have h1 : logb 10 (100 * (10 : ℝ)) = 2 + logb 10 (10 : ℝ) := by
        calc
          logb 10 (100 * (10 : ℝ))
              = logb 10 (100) + logb 10 (10 : ℝ) := by
                rw [logb_mul (by norm_num) (by norm_num)]
              _ = logb 10 (10 ^ (2 : ℝ)) + logb 10 (10 : ℝ) := by
                norm_num
              _ = 2 + logb 10 (10 : ℝ) := by
                rw [logb_rpow (by norm_num)]
                all_goals norm_num
      have h5 : logb 10 (10 : ℝ) = 1 := by 
        norm_num [logb_eq_iff_rpow_eq]
      have h2 : logb 10 (10 * (10 : ℝ)) = 1 + logb 10 (10 : ℝ) := by
        calc
          logb 10 (10 * (10 : ℝ))
              = logb 10 10 + logb 10 (10 : ℝ) := by 
                rw [logb_mul (by norm_num) (by norm_num)]
              _ = 1 + logb 10 (10 : ℝ) := by 
                norm_num
      have h3 : logb 10 (1 / (10 : ℝ)) = - logb 10 (10 : ℝ) := by 
        calc
          logb 10 (1 / (10 : ℝ))
              = logb 10 1 - logb 10 (10 : ℝ) := by 
                field_simp [logb_div]
              _ = 0 - logb 10 (10 : ℝ) := by 
                simp
              _ = - logb 10 (10 : ℝ) := by 
                ring
      rw [h1, h2, h3, h5]
      <;> nlinarith