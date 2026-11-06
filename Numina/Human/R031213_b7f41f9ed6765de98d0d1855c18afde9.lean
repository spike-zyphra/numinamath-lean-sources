import Mathlib

theorem algebra_52475 : Real.sqrt ((31 * 30 * 29 * 28 + 1)) = 869 := by 
    apply Real.sqrt_eq_cases.mpr
    simp
    norm_num