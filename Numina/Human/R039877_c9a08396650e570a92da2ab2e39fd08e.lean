import Mathlib

theorem sqrt_power_eval : (Real.sqrt ((Real.sqrt 3) ^ 3)) ^ 4 = 27 := by
  -- We simplify the expression step by step.
  calc
    -- $\left(\sqrt{(\sqrt3)^3}\right)^4$
    (Real.sqrt ((Real.sqrt 3) ^ 3)) ^ 4 = (3 ^ ((3 / 4 : ℝ))) ^ (4 : ℝ) := by
      -- Simplify the innermost power
      rw [show (Real.sqrt ((Real.sqrt 3) ^ 3)) ^ 4 = (Real.sqrt ((Real.sqrt 3) ^ (3 : ℝ))) ^ (4 : ℝ) by norm_cast, 
        Real.sqrt_eq_rpow, ← Real.rpow_mul (x := √3) (y := 3) (z := 1 / 2) (by norm_num), mul_one_div,
        ← Real.rpow_div_two_eq_sqrt _ (by norm_num), div_div]
      norm_num
    _ = 3 ^ 3 := by
      -- Apply the power of a power rule
      rw [← Real.rpow_mul (by norm_num)]
      norm_num
    _ = 27 := by
      -- Final simplification
      norm_num