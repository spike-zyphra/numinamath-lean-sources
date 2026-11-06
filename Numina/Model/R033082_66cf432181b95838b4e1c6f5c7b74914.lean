import Mathlib

theorem algebra_131002 : ∃ q : ℚ, (Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) -
    (Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3) = q := by

  have h1 : Real.sqrt 52 ≥ 0 := Real.sqrt_nonneg 52

  have h2 : Real.sqrt 52 ^ 2 = 52 := by
    calc
      Real.sqrt 52 ^ 2 = (Real.sqrt 52) ^ 2 := by ring
      _ = 52 := Real.sq_sqrt (by norm_num)
  
  have h3 : (Real.sqrt 52 + 5 : ℝ) * (Real.sqrt 52 - 5 : ℝ) = 27 := by
    nlinarith [h2, Real.sqrt_pos.mpr (show (52 : ℝ) > 0 by norm_num)]

  have h4 : ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) = 3 := by
    have h5 : ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) =
        ((Real.sqrt 52 + 5) * (Real.sqrt 52 - 5)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals
        nlinarith [Real.sqrt_nonneg 52, Real.sqrt_pos.mpr (show (52 : ℝ) > 0 by norm_num), h1]
    rw [h5]
    rw [h3]
    have h6 : (27 : ℝ) ^ ((1 : ℝ) / 3) = 3 := by
      rw [show (27 : ℝ) = 3 ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    rw [h6]

  have h5 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 10 - 9 * ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) := by
    have h7 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = Real.sqrt 52 + 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        nlinarith [Real.sqrt_nonneg 52, Real.sqrt_pos.mpr (show (52 : ℝ) > 0 by norm_num)]
    have h8 : ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = Real.sqrt 52 - 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        nlinarith [Real.sqrt_nonneg 52, Real.sqrt_pos.mpr (show (52 : ℝ) > 0 by norm_num)]
    have h9 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 - ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 - 3 * ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) * ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3))) * ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) := by
      ring
    rw [h9, h7, h8, h4]
    nlinarith [Real.sqrt_nonneg 52, Real.sqrt_pos.mpr (show (52 : ℝ) > 0 by norm_num), h2]

  have h10 : (Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3) = 1 := by
    have h8 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 9 * ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) - 10 = 0 := by
      linarith [h5]
    have h9 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3) - (1 : ℝ)) * (((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) + 10) = 0 := by
      nlinarith [h8]
    cases' (mul_eq_zero.1 h9) with h10 h11
    · -- Case $A - B - 1 = 0$, so $A - B = 1$.
      linarith
    · -- Case $(A - B)^2 + (A - B) + 10 = 0$, which is impossible since its discriminant is negative.
      nlinarith [sq_nonneg (((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) + 1 / 2 : ℝ)]

  use 1
  have eq1 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) = (1 : ℝ) := h10
  norm_num at eq1 ⊢
  all_goals try linarith [eq1]