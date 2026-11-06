import Mathlib

theorem algebra_154294 (z : ℂ) (hz : z = -2 + 2 * Real.sqrt 3 * .I) :
    z = 4 * (Real.cos (2 * Real.pi / 3) + .I * Real.sin (2 * Real.pi / 3)) := by
  rw [hz]
  have h1 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by 
    have h2 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by 
      ring 
    rw [h2]
    rw [Real.cos_pi_sub]
    have hcos : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    linarith [hcos]

  have h2 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by 
    have h3 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by 
      ring 
    rw [h3]
    rw [Real.sin_pi_sub]
    have hsin : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
      have hsin3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      linarith [hsin3]
    linarith [hsin]

  simp [Complex.ext_iff, h1, h2]
  all_goals
    ring_nf
    <;> field_simp
    <;> ring
    <;> simp [Real.sqrt_sq, Real.sq_sqrt]