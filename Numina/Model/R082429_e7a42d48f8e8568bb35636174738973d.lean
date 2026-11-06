import Mathlib

theorem algebra_286561 : (Real.sin (Real.pi / 8))^4 + (Real.sin (3 * Real.pi / 8))^4 +
    (Real.sin (5 * Real.pi / 8))^4 + (Real.sin (7 * Real.pi / 8))^4 = 3 / 2 := by
  have h1 : Real.sin (5 * Real.pi / 8) = Real.sin (3 * Real.pi / 8) := by
    have h2 : 5 * Real.pi / 8 = Real.pi - 3 * Real.pi / 8 := by
      ring
    rw [h2]
    rw [Real.sin_pi_sub]
  
  have h1' : Real.sin (7 * Real.pi / 8) = Real.sin (Real.pi / 8) := by
    have h2' : 7 * Real.pi / 8 = Real.pi - Real.pi / 8 := by
      ring
    rw [h2']
    rw [Real.sin_pi_sub]

  have h3 : (Real.sin (5 * Real.pi / 8))^4 = (Real.sin (3 * Real.pi / 8))^4 := by
    rw [h1]

  have h3' : (Real.sin (7 * Real.pi / 8))^4 = (Real.sin (Real.pi / 8))^4 := by
    rw [h1']

  have h4 : (Real.sin (Real.pi / 8))^4 + (Real.sin (3 * Real.pi / 8))^4 + (Real.sin (5 * Real.pi / 8))^4 + (Real.sin (7 * Real.pi / 8))^4 = 2 * ((Real.sin (Real.pi / 8))^4 + (Real.sin (3 * Real.pi / 8))^4) := by
    rw [h3, h3']
    ring
  
  have h5 : (Real.sin (Real.pi / 8))^4 + (Real.sin (3 * Real.pi / 8))^4 = 3 / 4 := by
    have hsin1 : Real.sin (Real.pi / 8) ^ 2 = (1 - Real.cos (Real.pi / 4)) / 2 := by
      have h3 : Real.sin (Real.pi / 8) ^ 2 = (1 - Real.cos (2 * (Real.pi / 8)) ) / 2 := by
        rw [Real.sin_sq_eq_half_sub]
        ring_nf
      rw [h3]
      ring_nf

    have hsin2 : Real.sin (3 * Real.pi / 8) ^ 2 = (1 + Real.cos (Real.pi / 4)) / 2 := by
      have h6 : Real.sin (3 * Real.pi / 8) ^ 2 = (1 - Real.cos (2 * (3 * Real.pi / 8)) ) / 2 := by
        rw [Real.sin_sq_eq_half_sub]
        ring_nf
      rw [h6]
      have h7 : 2 * (3 * Real.pi / 8) = Real.pi - Real.pi / 4 := by 
        ring
      rw [h7]
      have h8 : Real.cos (Real.pi - Real.pi / 4) = - Real.cos (Real.pi / 4) := by
        rw [Real.cos_pi_sub]
      rw [h8]
      all_goals ring_nf <;> field_simp <;> ring_nf <;> norm_num

    have h6 : (Real.sin (Real.pi / 8))^4 = ( (Real.sin (Real.pi / 8) )^2 )^2 := by ring
    have h7 : (Real.sin (3 * Real.pi / 8))^4 = ( (Real.sin (3 * Real.pi / 8) )^2 )^2 := by ring

    rw [h6, h7, hsin1, hsin2]

    have hcos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact Real.cos_pi_div_four

    rw [hcos]
    ring_nf
    <;> field_simp
    <;> ring_nf
    <;> norm_num

  linarith [h5, h4]