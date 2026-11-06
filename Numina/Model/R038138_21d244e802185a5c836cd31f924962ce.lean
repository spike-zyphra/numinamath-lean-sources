import Mathlib

theorem algebra_10508 (x : ℤ) : (2 : ℝ)^(x - 3) = (4 : ℝ)^(x + 1) ↔ x = -5 := by
  constructor
  · -- This is the forward direction: assuming (2 : ℝ)^(x - 3) = (4 : ℝ)^(x + 1) proving x = -5.
    intro h
    have h1 : (4 : ℝ) ^ (x + 1 : ℤ) = (2 : ℝ) ^ (2 * (x + 1 : ℤ) ) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) by norm_num]
      rw [← zpow_mul]
      all_goals ring
    rw [h1] at h 
    have h3 : (x - 3 : ℤ) = (2 * (x + 1) : ℤ) := by
      exact_mod_cast (by
        simpa using h
      )
    have h4 : x - 3 = 2 * (x + 1) := by 
      exact_mod_cast h3
    have hx : x = -5 := by 
      linarith 
    exact_mod_cast hx
  · -- This is the reverse direction: assuming x = -5 proving (2 : ℝ)^(x - 3) = (4 : ℝ)^(x + 1).
    intro h
    rw [show x = -5 by
      exact_mod_cast h
    ]
    norm_num