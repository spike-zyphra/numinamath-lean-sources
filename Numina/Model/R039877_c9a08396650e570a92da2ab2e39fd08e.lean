import Mathlib

theorem sqrt_power_eval : (Real.sqrt ((Real.sqrt 3) ^ 3)) ^ 4 = 27 := by
  have h1 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h2 : (Real.sqrt 3) ^ 3 = 3 * (Real.sqrt 3) := by
    calc
      (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * (Real.sqrt 3) := by ring
      _ = 3 * (Real.sqrt 3) := by
        rw [h1]

  have h3 : (Real.sqrt ((Real.sqrt 3) ^ 3)) ^ 2 = (Real.sqrt 3) ^ 3 := by
    rw [Real.sq_sqrt]
    have h_nonneg : 0 ≤ (Real.sqrt 3 : ℝ) ^ 3 := by positivity
    exact h_nonneg

  calc
    (Real.sqrt ((Real.sqrt 3) ^ 3)) ^ 4 = ((Real.sqrt ((Real.sqrt 3) ^ 3)) ^ 2) ^ 2 := by ring
    _ = ((Real.sqrt 3) ^ 3) ^ 2 := by rw [h3]
    _ = (3 * (Real.sqrt 3)) ^ 2 := by rw [h2]
    _ = 3 ^ 2 * ((Real.sqrt 3) ^ 2) := by ring
    _ = 3 ^ 2 * 3 := by rw [h1]
    _ = 27 := by norm_num