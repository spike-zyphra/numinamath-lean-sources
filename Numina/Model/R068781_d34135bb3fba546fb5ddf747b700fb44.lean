import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_599881 (a b : ℝ) (h : ∀ x : ℝ, a * cos x + b * cos (3 * x) ≤ 1) :
    |b| ≤ 1 := by
  have h1 := h 0
  have h3 := h Real.pi
  have h4 := h (Real.pi / 3)
  have h5 := h (2 * Real.pi / 3)
  have h7 : a + b ≤ 1 := by
    have h1' : a * cos (0 : ℝ) + b * cos (3 * (0 : ℝ)) ≤ 1 := h 0
    simp [cos_zero] at h1'
    linarith

  have h8 : -a - b ≤ 1 := by
    have h3' : a * cos Real.pi + b * cos (3 * Real.pi) ≤ 1 := h Real.pi
    have hcospi : cos Real.pi = -1 := cos_pi
    have hcos3pi : cos (3 * Real.pi) = -1 := by
      have h1 : 3 * Real.pi = Real.pi + 2 * Real.pi := by ring
      rw [h1]
      rw [cos_add, cos_two_pi, sin_two_pi]
      norm_num
    rw [hcospi, hcos3pi] at h3'
    nlinarith

  have h9 : a * (1 / 2) + b * (-1) ≤ 1 := by
    have h4' : a * cos (Real.pi / 3 : ℝ) + b * cos (3 * (Real.pi / 3 : ℝ)) ≤ 1 := h (Real.pi / 3)
    have hcos1 : cos (Real.pi / 3 : ℝ) = 1 / 2 := cos_pi_div_three
    have hcos2 : cos (3 * (Real.pi / 3 : ℝ)) = -1 := by
      have h1 : 3 * (Real.pi / 3 : ℝ) = Real.pi := by ring
      rw [h1]
      exact cos_pi
    rw [hcos1, hcos2] at h4'
    nlinarith

  have h10 : -a / 2 + b ≤ 1 := by
    have h5' : a * cos (2 * Real.pi / 3 : ℝ) + b * cos (3 * (2 * Real.pi / 3 : ℝ)) ≤ 1 := h (2 * Real.pi / 3)
    have hcos1 : cos (2 * Real.pi / 3 : ℝ) = -1 / 2 := by
      have h1 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      rw [h1]
      rw [cos_pi_sub]
      rw [cos_pi_div_three]
      ring
    have hcos2 : cos (3 * (2 * Real.pi / 3 : ℝ)) = 1 := by
      have h2 : 3 * (2 * Real.pi / 3 : ℝ) = 2 * Real.pi := by ring
      rw [h2]
      exact cos_two_pi
    rw [hcos1, hcos2] at h5'
    nlinarith
  
  have hb1 : b ≤ 1 := by
    nlinarith [h7, h8, h9, h10]

  have hb2 : -1 ≤ b := by
    nlinarith [h7, h8, h9, h10]

  apply abs_le.mpr
  constructor <;> linarith [hb1, hb2]