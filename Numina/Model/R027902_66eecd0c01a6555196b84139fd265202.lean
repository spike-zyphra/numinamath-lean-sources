import Mathlib

theorem algebra_172629 (θ : Real) : Real.sin (3 * θ) = 4 * Real.sin θ * Real.sin (Real.pi / 3 + θ) * Real.sin (2 * Real.pi / 3 + θ) := by 
  have h1 : Real.sin (3 * θ) = 3 * Real.sin θ - 4 * Real.sin θ ^ 3 := by
    rw [Real.sin_three_mul]
 
  have h2 : Real.sin (Real.pi / 3 + θ) = Real.sin (Real.pi / 3) * Real.cos θ + Real.cos (Real.pi / 3) * Real.sin θ := by
    rw [Real.sin_add]

  have h3 : Real.sin (2 * Real.pi / 3 + θ) = Real.sin (2 * Real.pi / 3) * Real.cos θ + Real.cos (2 * Real.pi / 3) * Real.sin θ := by 
    rw [Real.sin_add]

  have h4 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have h5 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three

  have h6 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by 
    have h1 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by 
      ring
    rw [h1, Real.sin_pi_sub]
    rw [Real.sin_pi_div_three]

  have h7 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have h1 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by 
      ring
    rw [h1, Real.cos_pi_sub]
    rw [Real.cos_pi_div_three]
    all_goals linarith

  rw [h1]
  rw [h2, h3]
  rw [h4, h5, h6, h7]
  have h8 : 4 * Real.sin θ * (Real.sqrt 3 / 2 * Real.cos θ + 1 / 2 * Real.sin θ) * (Real.sqrt 3 / 2 * Real.cos θ + -1 / 2 * Real.sin θ) = 
          Real.sin θ * (3 * Real.cos θ ^ 2 - Real.sin θ ^ 2) := by
    ring_nf
    <;> simp [pow_two, pow_three, Real.sqrt_sq] 
    <;> ring
  rw [h8]

  have h9 : Real.sin θ * (3 * Real.cos θ ^ 2 - Real.sin θ ^ 2) = 3 * Real.sin θ - 4 * Real.sin θ ^ 3 := by
    have hcos : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      have h1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ 
      linarith
    rw [hcos]
    ring

  linarith [h9]