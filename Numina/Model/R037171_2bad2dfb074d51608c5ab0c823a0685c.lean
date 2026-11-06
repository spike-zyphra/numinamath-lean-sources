import Mathlib

theorem algebra_123837 (x : ℝ) (hx : x = Real.pi / 4) :
    Real.sin (2017 * x) - Real.tan (2016 * x) = Real.cos (2015 * x) := by 
  rw [hx]
  have h1 : Real.sin (2017 * (Real.pi / 4)) = Real.sqrt 2 / 2 := by 
    have h2 : 2017 * (Real.pi / 4) = Real.pi / 4 + 504 * Real.pi := by 
      ring_nf
    rw [h2]
    have h3 : Real.sin (Real.pi / 4 + 504 * Real.pi) = Real.sin (Real.pi / 4) := by 
      have h4 : 504 * Real.pi = 252 * (2 * Real.pi) := by 
        ring_nf
      rw [h4]
      have h5 : Real.sin (Real.pi / 4 + 252 * (2 * Real.pi)) = Real.sin (Real.pi / 4) := by 
        have h6 : Real.sin (Real.pi / 4 + 252 * (2 * Real.pi)) = Real.sin (Real.pi / 4 + (252 : ℕ) * (2 * Real.pi)) := by 
          norm_cast
        rw [h6]
        rw [Real.sin_add_nat_mul_two_pi]
        all_goals try norm_num
      exact h5
    rw [h3]
    have h4 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    rw [h4]
    all_goals try norm_num
  have h2 : Real.cos (2015 * (Real.pi / 4)) = Real.sqrt 2 / 2 := by 
    have h3 : 2015 * (Real.pi / 4) = Real.pi + 3 * Real.pi / 4 + 251 * (2 * Real.pi) := by 
      ring_nf
    rw [h3]
    have h4 : Real.cos (Real.pi + 3 * Real.pi / 4 + 251 * (2 * Real.pi)) = Real.cos (Real.pi + 3 * Real.pi / 4) := by 
      have h5 : Real.cos (Real.pi + 3 * Real.pi / 4 + 251 * (2 * Real.pi)) = Real.cos (Real.pi + 3 * Real.pi / 4 + (251 : ℕ) * (2 * Real.pi)) := by 
        norm_cast
      rw [h5]
      rw [Real.cos_add_nat_mul_two_pi]
      all_goals try norm_num
    rw [h4]
    have h6 : Real.cos (Real.pi + 3 * Real.pi / 4) = - Real.cos (3 * Real.pi / 4) := by 
      rw [Real.cos_add]
      simp [Real.cos_pi, Real.sin_pi]
      all_goals ring_nf <;> norm_num
    rw [h6]
    have h7 : Real.cos (3 * Real.pi / 4) = - Real.sqrt 2 / 2 := by 
      have h8 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by 
        ring_nf
      rw [h8]
      rw [Real.cos_pi_sub]
      have h9 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      rw [h9]
      all_goals ring_nf <;> norm_num
    rw [h7]
    all_goals ring_nf
    <;> norm_num
  have h3 : Real.tan (2016 * (Real.pi / 4)) = 0 := by 
    have h4 : 2016 * (Real.pi / 4) = 504 * Real.pi := by 
      ring_nf
    rw [h4]
    have h5 : Real.tan (504 * Real.pi) = 0 := by 
      have h7 : 504 * Real.pi = (504 : ℤ) * Real.pi := by 
        simp
      rw [h7]
      rw [Real.tan_int_mul_pi]
      all_goals try norm_num
    exact h5 
  rw [h1, h3, h2]
  all_goals try norm_num
  <;> try linarith