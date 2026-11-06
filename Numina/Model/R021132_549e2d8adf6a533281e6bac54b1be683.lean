import Mathlib

open Real

theorem calculus_155562 (f : ℝ → ℝ) (hf : f = fun x => 2^x) :
    deriv f 1 = log 4 := by
  rw [hf]
  -- We need to compute the derivative of 2^x at x = 1.
  -- The derivative of a^x is a^x * ln(a).
  -- So the derivative of 2^x is 2^x * ln(2).
  -- At x = 1, this is 2^1 * ln(2) = 2 * ln(2).
  -- We need to show that 2 * ln(2) = ln(4).
  -- This is true because 4 = 2^2, so ln(4) = ln(2^2) = 2 * ln(2).
  have h1 : deriv (fun (x : ℝ) => (2 : ℝ) ^ x) 1 = (2 : ℝ) ^ (1 : ℝ) * (Real.log (2 : ℝ) ) := by
    simp [Real.rpow_def_of_pos, mul_comm]
  rw [h1]
  have h2 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by
    norm_num
  rw [h2]
  -- Now we need to show that 2 * log 2 = log 4
  have h3 : (2 : ℝ) * Real.log (2 : ℝ) = Real.log (4 : ℝ) := by
    have h4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
    linarith
  linarith