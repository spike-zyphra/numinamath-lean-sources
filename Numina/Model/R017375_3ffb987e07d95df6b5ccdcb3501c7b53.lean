import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_22069 {x y z : ℝ} (hx : x = 8) (hy : y = -3) (hz : z = -1)
  (ρ θ φ : ℝ) (hρ : ρ > 0) (hθ : θ ∈ Ioo (-π) π) (hφ : φ ∈ Ioo 0 π)
  (h : x = ρ * sin φ * cos θ) (h' : y = ρ * sin φ * sin θ) (h'' : z = ρ * cos φ) :
  (8, 3, -1) = (ρ * sin φ * cos (-θ), ρ * sin φ * sin (-θ), ρ * cos φ) := by
  have hx_eq : 8 = ρ * sin φ * cos θ := by 
    rw [hx] at h
    linarith
  have hy_eq : -3 = ρ * sin φ * sin θ := by 
    rw [hy] at h'
    linarith
  have hz_eq : -1 = ρ * cos φ := by 
    rw [hz] at h''
    linarith
  simp [cos_neg, sin_neg]
  constructor
  · -- Show 8 = ρ * sin φ * cos θ
    linarith [hx_eq]
  constructor
  · -- Show 3 = -(ρ * sin φ * sin θ)
    linarith [hy_eq]
  · -- Show -1 = ρ * cos φ
    linarith [hz_eq]