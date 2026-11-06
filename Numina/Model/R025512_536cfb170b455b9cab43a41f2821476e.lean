import Mathlib

theorem algebra_20378 : (100 / 101 : ℝ)^(-3 : ℝ) * (100 / 101)^3 = 1 := by
  have h1 : ( (100 / 101 : ℝ) ^ (-3 : ℝ) ) * ( (100 / 101) ^ 3 ) = 1 := by
    have h2 : (100 / 101 : ℝ) ^ (-3 : ℝ) = ( (101 / 100 : ℝ) ^ 3 ) := by 
      norm_num [Real.rpow_neg, Real.rpow_natCast]
    rw [h2]
    field_simp
    <;> norm_num
  exact h1