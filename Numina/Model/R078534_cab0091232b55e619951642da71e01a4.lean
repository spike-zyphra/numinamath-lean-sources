import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_138055 (f : ℝ → ℝ) (hf : f = λ x => (2 * x - sin (π * x / 2)) ^ ((1 : ℝ) / 4)) :
    deriv f 1 * (1.02 - 1) + f 1 = 1.01 := by

  have f1_val : f 1 = 1 := by
    rw [hf]
    norm_num [Real.rpow_natCast, Real.sin_pi_div_two, mul_comm]
    all_goals norm_num

  have hderiv : deriv f 1 = 1 / 2 := by
    rw [hf]
    simp [deriv_pow, deriv_sub, deriv_mul, deriv_id'', mul_comm]
    all_goals
      norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two, mul_comm]
      all_goals
        field_simp [Real.rpow_def_of_pos]
        <;> ring_nf <;> norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two]

  rw [hderiv, f1_val]
  norm_num