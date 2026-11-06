import Mathlib

open Polynomial

/-Find a nonzero monic polynomial P(x) with integer coefficients and minimal degree such that P(1 - 2^(1/3) + 4^(1/3)) = 0
(A polynomial is called monic if its leading coefficient is 1.)-/

noncomputable def P: ℝ[X] := X ^ 3 - 3 * X ^ 2 + 9 * X - 9

theorem Algebra_609252: P.eval (1 - 2 ^ (1/3: ℝ) + 4 ^ (1/3: ℝ)) = 0 := by

  have eq1 : (4 : ℝ) ^ (1 / 3 : ℝ) = ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    have h1 : (4 : ℝ) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) := by 
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h2 : (2 : ℝ) ^ (2 / 3 : ℝ) = ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h1, h2]

  have eq2 : (1 - (2 : ℝ) ^ (1 / 3 : ℝ) + (4 : ℝ) ^ (1 / 3 : ℝ)) =
    (1 - (2 : ℝ) ^ (1 / 3 : ℝ) + ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2) := by
    rw [eq1]

  have h1 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals norm_num
  
  have eq3 : ((1 - (2 : ℝ) ^ (1 / 3 : ℝ) + ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2) ^ 3 - 3 * (1 - (2 : ℝ) ^ (1 / 3 : ℝ) + ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2) ^ 2 + 9 * (1 - (2 : ℝ) ^ (1 / 3 : ℝ) + ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2) - 9) = 0 := by
    have eq00 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (2 : ℝ) := h1
    nlinarith [ sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) - 1), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) ^ 2 - (2 : ℝ) ^ (1 / 3 : ℝ)), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) ^ 2 - 1), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) - 2), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) ^ 2 - 2), Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (1 / 3), sq_nonneg ((2 : ℝ) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ (1 / 3 : ℝ) ^ 2 - 1)), sq_nonneg (((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 * ((2 : ℝ) ^ (1 / 3 : ℝ) - 1))]
  
  have eq4 : P.eval (1 - (2 : ℝ) ^ (1/3: ℝ) + (4 : ℝ) ^ (1/3: ℝ)) = 0 := by
    rw [eq2]
    simp [P] at *
    linarith [eq3]

  exact eq4