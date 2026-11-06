import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_173641 (a b : ℝ) (h : ∀ x : ℝ, a * cos x + b * cos (3 * x) ≤ 1) :
    |b| ≤ 1 := by

  have h1 := h 0
  have h2 := h (Real.pi)
  have h3 := h (Real.pi / 3)
  have h4 := h (2 * Real.pi / 3)

  have h1' : a * cos (0 : ℝ) + b * cos (3 * (0 : ℝ)) ≤ 1 := by
    simpa using h1

  have h2' : a * cos (Real.pi : ℝ) + b * cos (3 * (Real.pi : ℝ)) ≤ 1 := by 
    simpa using h2

  have h3' : a * cos (Real.pi / 3 : ℝ) + b * cos (3 * (Real.pi / 3 : ℝ)) ≤ 1 := by 
    simpa using h3

  have h4' : a * cos (2 * Real.pi / 3 : ℝ) + b * cos (3 * (2 * Real.pi / 3 : ℝ)) ≤ 1 := by
    simpa using h4

  have hcos1 : cos (0 : ℝ) = 1 := by 
    exact cos_zero

  have hcos1' : cos (3 * (0 : ℝ)) = 1 := by
    have h1 : 3 * (0 : ℝ) = (0 : ℝ) := by ring
    rw [h1]
    exact cos_zero

  have hcos2 : cos (Real.pi : ℝ) = -1 := by 
    exact cos_pi

  have hcos2' : cos (3 * (Real.pi : ℝ)) = -1 := by 
    have h1 : 3 * (Real.pi : ℝ) = 3 * Real.pi := by ring
    rw [h1]
    have h3 : 3 * Real.pi = Real.pi + 2 * Real.pi := by ring
    rw [h3]
    have h4 : cos (Real.pi + 2 * Real.pi) = cos (Real.pi) := by
      rw [cos_add_two_pi]
    rw [h4]
    exact cos_pi

  have hcos31 : cos (Real.pi / 3 : ℝ) = 1 / 2 := by 
    exact cos_pi_div_three

  have hcos32 : cos (3 * (Real.pi / 3 : ℝ)) = -1 := by
    have h1 : 3 * (Real.pi / 3 : ℝ) = Real.pi := by ring
    rw [h1]
    exact cos_pi

  have hcos41 : cos (2 * Real.pi / 3 : ℝ) = -1 / 2 := by
    have h1 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [h1]
    rw [cos_pi_sub]
    linarith [cos_pi_div_three]

  have hcos42 : cos (3 * (2 * Real.pi / 3 : ℝ)) = 1 := by 
    have h1 : 3 * (2 * Real.pi / 3 : ℝ) = 2 * Real.pi := by ring
    rw [h1]
    exact cos_two_pi

  rw [hcos1] at h1'
  rw [hcos1'] at h1'

  rw [hcos2] at h2'
  rw [hcos2'] at h2'

  rw [hcos31] at h3'
  rw [hcos32] at h3'

  rw [hcos41] at h4'
  rw [hcos42] at h4'

  have hb1 : a + b ≤ 1 := by
    nlinarith

  have hb2 : a + b ≥ -1 := by 
    nlinarith

  have hb3 : a / 2 - b ≤ 1 := by
    nlinarith

  have hb4 : -a / 2 + b ≤ 1 := by 
    nlinarith

  have hb5 : b ≤ 1 := by 
    nlinarith

  have hb6 : b ≥ -1 := by 
    nlinarith

  apply abs_le.mpr
  constructor <;> linarith [hb5, hb6]