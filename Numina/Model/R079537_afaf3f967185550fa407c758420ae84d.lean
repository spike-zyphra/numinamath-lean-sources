import Mathlib

theorem algebra_9521 : IsLeast {x | ∃ t : ℝ, x = - (Real.cos t)^2 + 4 * Real.sin t + 16} 12 := by
  constructor
  · -- Let's show 12 is in the set
    use Real.pi * (3 / 2)
    have h1 : Real.cos (Real.pi * (3 / 2)) = 0 := by
      have h1 : Real.cos (Real.pi * (3 / 2)) = Real.cos (Real.pi + Real.pi / 2) := by
        ring_nf
      rw [h1]
      rw [Real.cos_add]
      rw [Real.cos_pi, Real.sin_pi]
      norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
    have h2 : Real.sin (Real.pi * (3 / 2)) = -1 := by 
      have h2 : Real.sin (Real.pi * (3 / 2)) = Real.sin (Real.pi + Real.pi / 2) := by 
        ring_nf 
      rw [h2] 
      rw [Real.sin_add] 
      rw [Real.cos_pi, Real.sin_pi] 
      norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two] 
    rw [h1, h2]
    norm_num
  · -- Now we need to prove 12 is the smallest value
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
    have h2 : -1 ≤ Real.sin t ∧ Real.sin t ≤ 1 := Real.sin_mem_Icc t
    nlinarith [sq_nonneg (Real.sin t + 1), sq_nonneg (Real.cos t), sq_nonneg (Real.sin t - -1), sq_nonneg (Real.sin t - 1),
      h1, h2.1, h2.2]