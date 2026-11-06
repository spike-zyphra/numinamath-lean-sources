import Mathlib

theorem algebra_13725 : IsLeast {n : ℤ | n > Real.sqrt 300} 18 := by
  constructor
  · -- Show 18 is in the set
    show (18 : ℤ) > Real.sqrt 300
    have h1 : Real.sqrt 300 < (18 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    exact_mod_cast h1
  · -- Show 18 is the least integer in the set
    intro n hn
    have : (n : ℤ) > Real.sqrt 300 := by 
      simpa using hn
    have h2 : (n : ℝ) > Real.sqrt 300 := by 
      exact_mod_cast this 
    have h5 : Real.sqrt 300 > (17 : ℝ) := by 
      have h6 : Real.sqrt 289 = (17 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h7 : Real.sqrt 300 > Real.sqrt 289 := by
        apply Real.sqrt_lt_sqrt
        all_goals norm_num
      rw [h6] at h7
      linarith
    have h8 : (n : ℝ) > (17 : ℝ) := by linarith 
    have h9 : n > (17 : ℤ) := by 
      exact_mod_cast h8 
    omega