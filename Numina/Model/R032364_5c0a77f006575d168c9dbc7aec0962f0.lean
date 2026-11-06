import Mathlib

open Real


theorem algebra_9033
    {f g : ℝ → ℝ}
    (hf : f = fun x => exp x + x ^ 2 - x + sin x)
    (a b : ℝ)
    (hg : g = fun x => a * x + b)
    (hg1 : deriv g 0 = deriv f 0)
    (hg2 : g 0 = f 0) :
    g = fun x => x + 1 := by
  have h1 : deriv f 0 = 1 := by
    rw [hf]
    simp [deriv_add, deriv_sub, deriv_pow, deriv_id'', mul_comm]
    all_goals norm_num [Real.deriv_sin, deriv_id'', Real.deriv_exp]

  have h2 : deriv g 0 = a := by 
    rw [hg]
    simp [deriv_add, deriv_mul, deriv_id'', mul_comm a, mul_assoc]

  have h3 : a = 1 := by
    rw [h2] at hg1
    rw [h1] at hg1
    linarith

  have h4 : f 0 = 1 := by 
    rw [hf]
    norm_num

  have h5 : g 0 = 1 := by 
    linarith [hg2, h4]

  have h6 : b = 1 := by
    rw [hg] at h5 
    simp at h5 
    linarith

  ext x
  simp [hg, h3, h6]
  <;> all_goals linarith