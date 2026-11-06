import Mathlib

open Real

theorem algebra_143197 {x : ℝ} (hx : x = sqrt 2) :
    x^(x + 1)^2 * (x^(x - 1))^(x + 1) / (x^(x^2) / x^(-2 * x)) = 2 := by
  rw [hx]
  have h1 : Real.sqrt 2 > 0 := by
    positivity
  have h14 : (Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 + 1) ^ 2 : ℝ) * ((Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 - 1) : ℝ)) ^ ((Real.sqrt 2 + 1) : ℝ) / ((Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) / (Real.sqrt 2 : ℝ) ^ (-2 * (Real.sqrt 2 : ℝ) : ℝ)) = (2 : ℝ) := by
    have h15 : Real.sqrt 2 ^ ((Real.sqrt 2 + 1) ^ 2 : ℝ) * (Real.sqrt 2 ^ ((Real.sqrt 2 - 1) : ℝ)) ^ ((Real.sqrt 2 + 1) : ℝ) = (Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 + 1) ^ 2 + (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) : ℝ) := by
      have h17 : ((Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 - 1) : ℝ)) ^ ((Real.sqrt 2 + 1) : ℝ) = (Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals positivity
      rw [h17]
      have h16 : (Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 + 1) ^ 2 : ℝ) * (Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) : ℝ) = (Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 + 1) ^ 2 + (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) : ℝ) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals positivity
      rw [h16]
    have h17 : (Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) / (Real.sqrt 2 : ℝ) ^ (-2 * (Real.sqrt 2 : ℝ) : ℝ) = (Real.sqrt 2) ^ ((Real.sqrt 2 : ℝ) ^ 2 + 2 * (Real.sqrt 2 : ℝ) : ℝ) := by
      rw [← Real.rpow_sub]
      ring_nf
      all_goals positivity
    rw [h15, h17]
    have h18 : Real.sqrt 2 ^ ((Real.sqrt 2 + 1) ^ 2 + (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) : ℝ) / ((Real.sqrt 2) ^ ((Real.sqrt 2 : ℝ) ^ 2 + 2 * (Real.sqrt 2 : ℝ) : ℝ)) = (Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 + 1) ^ 2 + (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) - ((Real.sqrt 2) ^ 2 + 2 * (Real.sqrt 2) ) : ℝ) := by
      rw [← Real.rpow_sub]
      ring_nf
      all_goals positivity
    rw [h18]
    have h19 : (Real.sqrt 2 + 1 : ℝ) ^ 2 + (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) - ((Real.sqrt 2 : ℝ) ^ 2 + 2 * (Real.sqrt 2 : ℝ) ) = (Real.sqrt 2 : ℝ) ^ 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h19]
    have h77 : (Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) = (2 : ℝ) := by
      have h14 : (Real.sqrt 2 : ℝ) ^ ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) = (Real.sqrt 2 : ℝ) ^ (2 : ℝ) := by
        have h18 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := by
          rw [Real.sq_sqrt]
          positivity
        rw [h18]
      rw [h14]
      have h17 : (Real.sqrt 2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) := by
        calc
          (Real.sqrt 2 : ℝ) ^ (2 : ℝ) = ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) := by norm_cast
          _ = (2 : ℝ) := by
            rw [Real.sq_sqrt]
            positivity
      rw [h17]
    rw [h77]
  exact h14