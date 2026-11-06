import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_278094 (a b : ℝ) (h : ∀ x : ℝ, a * cos x + b * cos (3 * x) ≤ 1) :
    |b| ≤ 1 := by
  have h1 := h 0
  have h2 := h (Real.pi / 3)
  have h3 := h (2 * Real.pi / 3)
  have h4 := h Real.pi
  have h_eq1 : a + b ≤ 1 := by
    simp [Real.cos_zero, show 3 * (0 : ℝ) = (0 : ℝ) by ring, Real.cos_zero] at h1
    linarith
  -- For x = π/3
  have h_eq2 : a / 2 - b ≤ 1 := by
    have h1 : a * cos (Real.pi / 3) + b * cos (3 * (Real.pi / 3)) ≤ 1 := by 
      simpa using h2
    have h11 : cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    have h12 : cos (3 * (Real.pi / 3)) = -1 := by
      have h2 : 3 * (Real.pi / 3) = Real.pi := by ring
      rw [h2]
      norm_num [Real.cos_pi]
    simp only [h11, h12] at h1
    linarith
  -- For x = 2π/3
  have h_eq3 : -a / 2 + b ≤ 1 := by
    have h1 : a * cos (2 * Real.pi / 3) + b * cos (3 * (2 * Real.pi / 3)) ≤ 1 := by 
      simpa using h3
    have h11 : cos (2 * Real.pi / 3) = -1 / 2 := by
      have h2 : 2 * Real.pi / 3 = Real.pi - (Real.pi / 3) := by ring
      rw [h2]
      rw [Real.cos_pi_sub]
      norm_num [Real.cos_pi_div_three]
    have h12 : cos (3 * (2 * Real.pi / 3)) = 1 := by
      have h2 : 3 * (2 * Real.pi / 3) = 2 * Real.pi := by ring
      rw [h2]
      norm_num [Real.cos_two_pi]
    simp only [h11, h12] at h1
    linarith
  -- For x = π
  have h_eq4 : -a - b ≤ 1 := by
    have h1 : a * cos Real.pi + b * cos (3 * Real.pi) ≤ 1 := by 
      simpa using h4
    have h11 : cos Real.pi = -1 := Real.cos_pi
    have h12 : cos (3 * Real.pi) = -1 := by
      have h2 : 3 * Real.pi = 2 * Real.pi + Real.pi := by ring
      rw [h2]
      have h3 : cos (2 * Real.pi + Real.pi) = cos (Real.pi) := by
        rw [show 2 * Real.pi + Real.pi = Real.pi + 2 * Real.pi by ring]
        rw [Real.cos_add_two_pi]
      rw [h3]
      norm_num [Real.cos_pi]
    simp only [h11, h12] at h1
    linarith
  have h5 : -1 ≤ b := by
    linarith
  have h6 : b ≤ 1 := by
    linarith
  apply abs_le.mpr
  constructor <;> linarith
  all_goals linarith