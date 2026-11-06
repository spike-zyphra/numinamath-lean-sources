import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_23338 (x y z : ℝ) (hx : x = 12) (hy : y = -4) (hz : z = 3)
  (ρ θ φ : ℝ) (hρ : ρ > 0) (hθ : θ ∈ Ioo (-π) π) (hφ : φ ∈ Ioo 0 π)
  (h : x = ρ * sin φ * cos θ) (h' : y = ρ * sin φ * sin θ) (h'' : z = ρ * cos φ) :
  cos φ = 3 / 13 := by
  rw [mem_Ioo] at hθ hφ
  have eq1 : (x : ℝ)^2 + (y : ℝ)^2 + (z : ℝ)^2 = (ρ : ℝ)^2 := by 
    have eq2 : (x : ℝ)^2 + (y : ℝ)^2 = (ρ * sin φ) ^ 2 := by 
      calc 
        (x : ℝ)^2 + (y : ℝ)^2 = (x : ℝ)^2 + (y : ℝ)^2 := by ring
        _ = (ρ * sin φ * cos θ) ^ 2 + (ρ * sin φ * sin θ) ^ 2 := by rw [h, h']
        _ = (ρ * sin φ) ^ 2 * (cos θ ^ 2 + sin θ ^ 2) := by ring
        _ = (ρ * sin φ) ^ 2 * 1 := by 
          have h1 : cos θ ^ 2 + sin θ ^ 2 = 1 := by 
            exact Real.cos_sq_add_sin_sq θ
          rw [h1]
        _ = (ρ * sin φ) ^ 2 := by 
          ring
    calc 
      (x : ℝ)^2 + (y : ℝ)^2 + (z : ℝ)^2 = ((x : ℝ)^2 + (y : ℝ)^2) + (z : ℝ)^2 := by ring
      _ = (ρ * sin φ) ^ 2 + (z : ℝ)^2 := by rw [eq2]
      _ = (ρ * sin φ) ^ 2 + (ρ * cos φ) ^ 2 := by rw [h'']
      _ = (ρ : ℝ)^2 * (sin φ ^ 2 + cos φ ^ 2) := by 
        calc 
          (ρ * sin φ) ^ 2 + (ρ * cos φ) ^ 2 = (ρ : ℝ)^2 * sin φ ^ 2 + (ρ : ℝ)^2 * cos φ ^ 2 := by ring
          _ = (ρ : ℝ)^2 * (sin φ ^ 2 + cos φ ^ 2) := by ring
      _ = (ρ : ℝ)^2 * 1 := by 
        have h1 : sin φ ^ 2 + cos φ ^ 2 = 1 := by 
          exact Real.sin_sq_add_cos_sq φ
        rw [h1]
      _ = (ρ : ℝ)^2 := by ring
  rw [hx, hy, hz] at eq1
  have h1 : (ρ : ℝ) = 13 := by 
    nlinarith [eq1, hρ]
  have eq2 : cos φ = (z / ρ) := by 
    have eq3 : z = ρ * cos φ := by
      linarith [h'']
    have h2 : ρ > 0 := by linarith [hρ]
    have eq4 : cos φ = z / ρ := by 
      field_simp [h2] at *
      all_goals linarith [eq3]
    linarith [eq4]
  rw [eq2, hz, h1]
  all_goals norm_num