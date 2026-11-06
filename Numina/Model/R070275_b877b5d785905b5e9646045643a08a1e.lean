import Mathlib

open Real Set
open scoped Real

theorem algebra_176698 :
  IsLeast {x | ∃ t : ℝ, x = 3 * (sin t)^2 + 5 * (cos t)^2 + 2 * cos t} 2.5 := by 
  constructor
  · -- First we need to show that 2.5 can be obtained, i.e., there exists some real number t such that the function equals 2.5
    use 2 * Real.pi / 3
    have hsin : sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      have h1 : sin (2 * Real.pi / 3) = sin (Real.pi - Real.pi / 3) := by
        ring_nf
      rw [h1]
      rw [sin_pi_sub]
      have h3 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
        exact sin_pi_div_three
      rw [h3]
    
    have hcos : cos (2 * Real.pi / 3) = -1 / 2 := by 
      have h1 : cos (2 * Real.pi / 3) = cos (Real.pi - Real.pi / 3) := by
        ring_nf
      rw [h1]
      rw [cos_pi_sub]
      have h3 : cos (Real.pi / 3) = 1 / 2 := by 
        exact cos_pi_div_three
      rw [h3]
      all_goals ring

    rw [hsin, hcos]
    have h1 : (Real.sqrt 3 / 2 : ℝ) ^ 2 = 3 / 4 := by
      calc
        (Real.sqrt 3 / 2 : ℝ) ^ 2 = (Real.sqrt 3) ^ 2 / 4 := by ring
        _ = 3 / 4 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    
    have h2 : (-1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num

    nlinarith [h1, h2]
  
  · -- Now we need to prove that 2.5 is indeed the minimum
    intro x hx
    rcases hx with ⟨t, ht⟩
    
    have h1 : sin t ^ 2 + cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
    have h2 : sin t ^ 2 = 1 - cos t ^ 2 := by linarith [h1]
    
    rw [h2] at ht
    nlinarith [sq_nonneg (cos t + 1 / 2)]