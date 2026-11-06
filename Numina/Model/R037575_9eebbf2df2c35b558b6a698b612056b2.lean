import Mathlib

open Real Set
open scoped Real

theorem algebra_316132 (x : ℝ) : sin (π / (1 + x ^ 2)) = 0 ↔ x = 0 := by
  constructor 
  · -- Forward direction: If sin (π / (1 + x ^ 2)) = 0, then x = 0.
    intro h
    by_cases h1 : x = 0 
    · -- If x = 0, then it's true.
      exact h1 
    · -- Assume x ≠ 0.
      have h2 : x ≠ 0 := h1
      -- Then 1 + x^2 > 1.
      have h3 : 1 + x ^ 2 > 1 := by 
        have hx2_pos : x ^ 2 > 0 := by
          apply sq_pos_of_ne_zero 
          exact h2 
        linarith 
      -- The argument π/(1+x^2) is positive.
      have h4 : π / (1 + x^2) > 0 := by 
        apply div_pos 
        linarith [Real.pi_pos] 
        nlinarith [sq_nonneg x]
      -- The argument π/(1+x^2) is less than π.
      have h5 : π / (1 + x^2) < π := by 
        have h6 : 1 + x ^ 2 > (1 : ℝ) := h3 
        have hx12 : (1 + x ^ 2) > 0 := by nlinarith 
        have hx13 : π > 0 := Real.pi_pos 
        apply (div_lt_iff' (by positivity)).mpr
        nlinarith [Real.pi_pos, h6]
      -- Since 0 < π/(1+x^2) < π, we have sin(π/(1+x^2)) > 0.
      have h8 : sin (π / (1 + x^2)) > 0 := by
        apply sin_pos_of_pos_of_lt_pi 
        all_goals
        try linarith
      -- This contradicts the hypothesis that sin(π/(1+x^2)) = 0.
      linarith 
  · -- Backward direction: If x = 0, then sin(π/(1+x^2)) = 0.
    intro h 
    rw [h] 
    norm_num 
    <;> field_simp <;> norm_num [Real.sin_pi]