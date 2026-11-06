import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9331 {f : ℝ → ℝ} (hf : f = λ x => x * sin x) :
    deriv f (Real.pi/4) = Real.sqrt 2 / 2 + Real.sqrt 2 * Real.pi / 8 := by 
  rw [hf]
  have hderiv : deriv (λ (x : ℝ) => x * sin x) (Real.pi / 4) = sin (Real.pi / 4) + (Real.pi / 4) * cos (Real.pi / 4) := by
    rw [deriv_mul (differentiableAt_id) (by apply differentiableAt_sin)]
    all_goals simp
    all_goals ring_nf
    all_goals norm_num
    all_goals linarith [Real.pi_pos]
  rw [hderiv]
  have hsin : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have hcos : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  rw [hsin, hcos]
  ring_nf
  <;> field_simp
  <;> ring