import Mathlib

open Real

  theorem calculus_123832 (f : ℝ → ℝ) (hf : f = fun x => sqrt (x ^ 3)) (x : ℝ) (hx : x = 0.98) :
    deriv f 1 * (x - 1) + f 1 = 0.97 := by
  have h1 : f = fun x => Real.sqrt (x ^ 3) := by
    exact_mod_cast hf
  have h2 : f 1 = 1 := by
    rw [h1]
    norm_num [Real.sqrt_eq_cases]
  have h3 : deriv f 1 = 3 / 2 := by
    rw [h1]
    simp [deriv_sqrt, deriv_pow, mul_comm]
    all_goals norm_num
  rw [h3, h2, hx]
  norm_num