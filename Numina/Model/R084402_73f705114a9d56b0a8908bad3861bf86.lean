import Mathlib

open Real

theorem calculus_12297 (ρ θ φ : ℝ) (h₀ : ρ = 12) (h₁ : θ = 7 * π / 6) (h₂ : φ = π / 3) :
    let x := ρ * sin φ * cos θ
    let y := ρ * sin φ * sin θ
    let z := ρ * cos φ
    (x, y, z) = (-9, -3 * sqrt 3, 6) := by
  rw [h₀, h₁, h₂]
  have h3 : sin (π / 3) = sqrt 3 / 2 := by
    rw [sin_pi_div_three]
  have h4 : cos (π / 3) = 1 / 2 := by
    rw [cos_pi_div_three]
  have h5 : sin (7 * π / 6) = -1 / 2 := by
    have h6 : 7 * π / 6 = π + π / 6 := by
      ring
    rw [h6]
    rw [sin_add]
    rw [sin_pi, cos_pi]
    have h7 : sin (π / 6) = 1 / 2 := by 
      rw [sin_pi_div_six]
    have h8 : cos (π / 6) = Real.sqrt 3 / 2 := by 
      rw [cos_pi_div_six]
    rw [h7, h8]
    ring
  have h9 : cos (7 * π / 6) = -Real.sqrt 3 / 2 := by
    have h10 : 7 * π / 6 = π + π / 6 := by
      ring
    rw [h10]
    rw [cos_add]
    rw [cos_pi, sin_pi]
    have h11 : cos (π / 6) = Real.sqrt 3 / 2 := by 
      rw [cos_pi_div_six]
    have h12 : sin (π / 6) = 1 / 2 := by 
      rw [sin_pi_div_six]
    rw [h11, h12]
    ring
  simp [h3, h4, h5, h9]
  <;> ring_nf <;> norm_num <;> ring
  <;> nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]