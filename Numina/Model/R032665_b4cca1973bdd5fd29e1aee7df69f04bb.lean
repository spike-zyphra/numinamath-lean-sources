import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_9758 {f : ℝ → ℝ} (hf : Differentiable ℝ f)
  (h : ∀ x, f x = 2 * cos (x - π / 2) + deriv f 0 * cos x) :
  deriv f (3 * π / 4) = -2 * sqrt 2 := by
  let f0 := deriv f 0
  have h_eq : f = fun x => 2 * cos (x - π / 2) + f0 * cos x := by
    funext x
    exact h x
  have h1 : f = fun x => 2 * sin x + f0 * cos x := by
    funext x
    rw [h_eq]
    have h2 : cos (x - π / 2) = sin x := by
      rw [cos_sub_pi_div_two]
    simp [h2]
    <;> ring
  have h2 : deriv f 0 = f0 := by
    simpa
  have h3 : deriv f 0 = 2 := by
    have eq1 : deriv f 0 = 2 * cos 0 - f0 * sin 0 := by
      rw [h1] at *
      simp [deriv_add, deriv_mul, deriv_id'', mul_comm f0, differentiableAt_cos]
      all_goals
        try linarith
    rw [eq1]
    norm_num [cos_zero, sin_zero]
  have hf0 : f0 = 2 := by linarith [h2, h3]
  have eq2 : deriv f (3 * π / 4) = 2 * cos (3 * π / 4) - f0 * sin (3 * π / 4) := by
    rw [h1] at *
    simp [deriv_add, deriv_mul, deriv_id'', mul_comm f0, differentiableAt_cos]
    all_goals
      try linarith
  rw [hf0] at eq2
  have h4 : cos (3 * π / 4) = -Real.sqrt 2 / 2 := by
    have h4 : 3 * π / 4 = π - π / 4 := by 
      linarith [Real.pi_pos]
    rw [h4]
    rw [cos_pi_sub]
    have h5 : cos (π / 4) = Real.sqrt 2 / 2 := by 
      exact cos_pi_div_four
    rw [h5]
    <;> ring_nf <;> norm_num
  have h6 : sin (3 * π / 4) = Real.sqrt 2 / 2 := by 
    have h4 : 3 * π / 4 = π - π / 4 := by 
      linarith [Real.pi_pos]
    rw [h4]
    rw [sin_pi_sub]
    have h7 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      exact sin_pi_div_four
    rw [h7]
  rw [eq2]
  rw [h4, h6]
  ring_nf <;> norm_num
  <;> ring