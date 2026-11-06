import Mathlib

theorem algebra_165046 (α : ℝ) :
    Real.sin (250 * Real.pi / 180 + α) * Real.cos (200 * Real.pi / 180 - α) -
    Real.cos (240 * Real.pi / 180) * Real.cos (220 * Real.pi / 180 - 2 * α) =
    1 / 2 := by
  have h1 : Real.sin (250 * Real.pi / 180 + α) = - Real.sin (70 * Real.pi / 180 + α) := by
    have h2 : (250 * Real.pi / 180 + α) = Real.pi + (70 * Real.pi / 180 + α) := by ring
    rw [h2]
    rw [Real.sin_add, Real.sin_pi, Real.cos_pi]
    ring
  have h2 : Real.cos (200 * Real.pi / 180 - α) = - Real.cos (20 * Real.pi / 180 - α) := by
    have h3 : (200 * Real.pi / 180 - α) = Real.pi + (20 * Real.pi / 180 - α) := by ring
    rw [h3]
    rw [Real.cos_add, Real.sin_pi, Real.cos_pi]
    ring
  have h3 : Real.cos (240 * Real.pi / 180) = - 1 / 2 := by
    have h4 : (240 * Real.pi / 180 : ℝ) = Real.pi + (60 * Real.pi / 180 : ℝ) := by ring
    rw [h4]
    rw [Real.cos_add, Real.sin_pi, Real.cos_pi]
    have h5 : Real.cos (60 * Real.pi / 180) = 1 / 2 := by 
      have h6 : (60 * Real.pi / 180 : ℝ) = Real.pi / 3 := by ring
      rw [h6]
      exact Real.cos_pi_div_three
    linarith
  have h4 : Real.cos (220 * Real.pi / 180 - 2 * α) = - Real.cos (40 * Real.pi / 180 - 2 * α) := by
    have h5 : (220 * Real.pi / 180 - 2 * α : ℝ) = Real.pi + (40 * Real.pi / 180 - 2 * α : ℝ) := by ring
    rw [h5]
    rw [Real.cos_add, Real.sin_pi, Real.cos_pi]
    ring
  rw [h1, h2, h3, h4]
  have h5 : Real.sin (70 * Real.pi / 180 + α) = Real.cos (20 * Real.pi / 180 - α) := by
    have h6 : 70 * Real.pi / 180 + α = Real.pi / 2 - (20 * Real.pi / 180 - α) := by ring_nf
    rw [h6]
    rw [Real.sin_pi_div_two_sub]
  have h6 : Real.cos (40 * Real.pi / 180 - 2 * α) = 2 * (Real.cos (20 * Real.pi / 180 - α))^2 - 1 := by
    have h7 : 40 * Real.pi / 180 - 2 * α = 2 * (20 * Real.pi / 180 - α) := by ring_nf
    rw [h7]
    rw [Real.cos_two_mul]
  rw [h5, h6]
  nlinarith [Real.cos_sq_add_sin_sq (20 * Real.pi / 180 - α)]