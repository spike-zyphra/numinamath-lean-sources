import Mathlib

open Real

theorem calculus_15325 : ∑ i ∈ Finset.range 91, (cos (i * π / 180))^2 = 91 / 2 := by 
  have h2 : ∀ i, cos (i * π / 180)^2 + cos ((90 - i) * π / 180)^2 = 1 := by
    intro i
    have h3 : cos ((90 - i) * π / 180) = sin (i * π / 180) := by
      have h4 : (90 - i) * π / 180 = π / 2 - i * π / 180 := by
        ring
      rw [h4]
      rw [cos_pi_div_two_sub]
    have h6 : cos (i * π / 180)^2 + cos ((90 - i) * π / 180)^2 = cos (i * π / 180)^2 + sin (i * π / 180)^2 := by
      rw [h3]
    rw [h6]
    have h7 : cos (i * π / 180)^2 + sin (i * π / 180)^2 = 1 := by
      exact Real.cos_sq_add_sin_sq (i * π / 180)
    linarith
  have h3 : ∑ i in Finset.range 91, (cos (i * π / 180))^2 = 
      (∑ i in Finset.range 45, (cos (i * π / 180)^2 + cos ((90 - i) * π / 180)^2)) + cos (45 * π / 180)^2 := by
    simp [Finset.sum_range_succ]
    <;> ring
  rw [h3]
  have h4 : ∑ i in Finset.range 45, (cos (i * π / 180)^2 + cos ((90 - i) * π / 180)^2) = 45 := by
    have h5 : ∀ i, cos (i * π / 180)^2 + cos ((90 - i) * π / 180)^2 = 1 := h2
    simp [Finset.sum_range_succ, h5]
    <;> norm_num
  rw [h4]
  have h5 : cos (45 * π / 180)^2 = 1 / 2 := by
    have h6 : 45 * π / 180 = Real.pi / 4 := by 
      linarith [Real.pi_pos]
    rw [h6]
    have h7 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
      exact cos_pi_div_four
    rw [h7]
    have h8 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring
        _ = 2 / 4 := by 
          rw [Real.sq_sqrt]
          all_goals linarith
        _ = 1 / 2 := by norm_num
    linarith [h8]
  rw [h5]
  all_goals norm_num