import Mathlib

open Real Set
open scoped Real

theorem calculus_22982 (θ : Real) (h : sin (θ + π / 4) = 1 / 3) : sin (2 * θ) = -7 / 9 := by
  have h1 : sin (2 * θ) = - cos (2 * (θ + π / 4)) := by
    have h2 : 2 * θ = 2 * (θ + π / 4) - π / 2 := by
      ring_nf
    rw [h2]
    have h3 : sin (2 * (θ + π / 4) - π / 2) = sin (2 * (θ + π / 4)) * cos (π / 2) - cos (2 * (θ + π / 4)) * sin (π / 2) := by
      rw [sin_sub]
    rw [h3]
    have h4 : cos (π / 2) = 0 := by
      rw [cos_pi_div_two]
    have h5 : sin (π / 2) = 1 := by
      rw [sin_pi_div_two]
    rw [h4, h5]
    <;> simp
    <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
    <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
    <;> ring
  rw [h1]
  have h6 : cos (2 * (θ + π / 4)) = 1 - 2 * (sin (θ + π / 4))^2 := by
    have hcos : cos (2 * (θ + π / 4)) = 2 * (cos (θ + π / 4))^2 - 1 := by 
      rw [cos_two_mul]
    have hsin_sq : (sin (θ + π / 4))^2 = 1 - (cos (θ + π / 4))^2 := by
      rw [sin_sq]
    rw [hcos]
    rw [hsin_sq]
    ring
  rw [h6, h]
  norm_num