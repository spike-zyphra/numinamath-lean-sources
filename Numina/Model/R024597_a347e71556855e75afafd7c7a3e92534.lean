import Mathlib

theorem algebra_299118 (θ : ℝ) :
    Real.sin θ * Real.sin (Real.pi / 2 - θ) +
    (Real.sin (Real.pi / 4 + θ))^2 -
    (Real.sin (Real.pi / 6 - θ))^2 -
    (1 / 2) * Real.sin (Real.pi / 6 + 2 * θ) =
    Real.sin (2 * θ) := by

  have h1 : Real.sin (Real.pi / 2 - θ) = Real.cos θ := by 
    rw [Real.sin_pi_div_two_sub]
  have h2 : Real.sin (Real.pi / 4 + θ) = Real.sin (Real.pi / 4) * Real.cos θ + Real.cos (Real.pi / 4) * Real.sin θ := by 
    rw [Real.sin_add]
  have h3 : Real.sin (Real.pi / 6 - θ) = Real.sin (Real.pi / 6) * Real.cos θ - Real.cos (Real.pi / 6) * Real.sin θ := by 
    rw [Real.sin_sub]
  have h4 : Real.sin (Real.pi / 6 + 2 * θ) = Real.sin (Real.pi / 6) * Real.cos (2 * θ) + Real.cos (Real.pi / 6) * Real.sin (2 * θ) := by 
    rw [Real.sin_add]
  have h5 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := by 
    rw [Real.sin_two_mul]
  have h6 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have h7 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h8 : Real.sin (Real.pi / 6) = 1 / 2 := by 
    exact Real.sin_pi_div_six
  have h9 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by 
    exact Real.cos_pi_div_six
  rw [h1, h2, h3, h4, h5]
  rw [h6, h7, h8, h9]
  have h10 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h11 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by 
    rw [Real.cos_two_mul]
  simp [h11, h10]
  <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq, h10]
  <;> ring_nf