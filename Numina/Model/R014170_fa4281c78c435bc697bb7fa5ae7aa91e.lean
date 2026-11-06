import Mathlib

open Real Set
open scoped Real

theorem algebra_97638 (f : ℝ → ℝ) (hf : f = λ A => sin (A / 2) - sqrt 3 * cos (A / 2)) :
    IsLeast {x | ∃ A, x = f A} (f (-60 * π / 180)) := by 
  have h1 : ∀ A, f A = sin (A / 2) - sqrt 3 * cos (A / 2) := by
    intro A 
    rw [hf]
  have h2 : f (-60 * π / 180) = -2 := by 
    rw [h1]
    have h3 : (-60 * π / 180 : ℝ) / 2 = - (π / 6) := by 
      linarith [pi_pos]
    rw [h3]
    have h4 : sin (- (π / 6)) = -1 / 2 := by 
      have hsin : sin (- (π / 6)) = - sin (π / 6) := by 
        rw [show - (π / 6) = - (π / 6) by ring]
        rw [sin_neg]
      rw [hsin]
      rw [sin_pi_div_six]
      all_goals norm_num
    have h5 : cos (- (π / 6)) = Real.sqrt 3 / 2 := by 
      have hcos : cos (- (π / 6)) = cos (π / 6) := by 
        rw [show - (π / 6) = - (π / 6) by ring]
        rw [cos_neg]
      rw [hcos]
      rw [cos_pi_div_six]
    simp only [h4, h5]
    have h6 : sqrt 3 ^ 2 = 3 := by 
      rw [Real.sq_sqrt]
      linarith [show (0 : ℝ) ≤ (3 : ℝ) by norm_num]
    nlinarith [h6, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  
  constructor
  · -- Show f(-60 * π / 180) is in the image
    use -60 * π / 180 
    all_goals simp [h2]

  · -- Show f(-60 * π / 180) is the least element in the image 
    intro x hx 
    rcases hx with ⟨A, hA⟩ 
    rw [h1 A] at hA 
    have h7 : sin (A / 2) - sqrt 3 * cos (A / 2) ≥ -2 := by
      have h8 : sin (A / 2) - sqrt 3 * cos (A / 2) = 2 * sin ((A / 2) - (π / 3)) := by
        have h9 : sin ((A / 2) - (π / 3)) = sin (A / 2) * cos (π / 3) - cos (A / 2) * sin (π / 3) := by
          rw [sin_sub]
        rw [h9]
        have h10 : cos (π / 3) = 1 / 2 := by 
          exact cos_pi_div_three
        have h11 : sin (π / 3) = Real.sqrt 3 / 2 := by 
          exact sin_pi_div_three
        rw [h10, h11]
        ring_nf 
      have h9 : -1 ≤ sin ((A / 2) - (π / 3)) ∧ sin ((A / 2) - (π / 3)) ≤ 1 := by 
        apply sin_mem_Icc 
      linarith 
    linarith [h2, h7, hA]