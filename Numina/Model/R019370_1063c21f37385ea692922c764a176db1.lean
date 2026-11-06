import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_39817 {a b : ℝ} (h : ∀ x : ℝ, a * cos x + b * cos (3 * x) ≤ 1) :
    |b| ≤ 1 := by
  have h1 := h 0
  have h2 := h (Real.pi)
  have h3 := h (Real.pi / 3)
  have h4 := h (2 * Real.pi / 3)
  have hcos1 : cos (0 : ℝ) = 1 := Real.cos_zero
  have hcos1' : cos (3 * (0 : ℝ)) = 1 := by
    simp [show 3 * (0 : ℝ) = (0 : ℝ) by ring, Real.cos_zero]
  have hcos2 : cos (Real.pi : ℝ) = -1 := Real.cos_pi
  have hcos2' : cos (3 * (Real.pi : ℝ)) = -1 := by
    have : 3 * (Real.pi : ℝ) = 3 * Real.pi := by ring
    rw [this]
    have h1 : cos (3 * Real.pi) = -1 := by
      have h2 : 3 * Real.pi = Real.pi + 2 * Real.pi := by
        linarith [Real.pi_pos]
      rw [h2]
      rw [cos_add, cos_two_pi, sin_two_pi]
      norm_num
      all_goals linarith [Real.pi_pos]
    linarith
  have hcos3 : cos (Real.pi / 3 : ℝ) = 1 / 2 := Real.cos_pi_div_three
  have hcos3' : cos (3 * (Real.pi / 3 : ℝ)) = -1 := by
    have : 3 * (Real.pi / 3 : ℝ) = Real.pi := by
      ring_nf
    rw [this]
    linarith [Real.cos_pi]
  have hcos4 : cos (2 * Real.pi / 3 : ℝ) = -1 / 2 := by
    have h1 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by
      linarith [Real.pi_pos]
    rw [h1]
    rw [cos_pi_sub]
    linarith [Real.cos_pi_div_three]
  have hcos4' : cos (3 * (2 * Real.pi / 3 : ℝ)) = 1 := by
    have : 3 * (2 * Real.pi / 3 : ℝ) = 2 * Real.pi := by
      ring_nf
    rw [this]
    linarith [Real.cos_two_pi]
  simp [hcos1, hcos1'] at h1
  simp [hcos2, hcos2'] at h2
  simp [hcos3, hcos3'] at h3
  simp [hcos4, hcos4'] at h4
  have h5 : b ≤ 1 := by
    nlinarith
  have h6 : b ≥ -1 := by
    nlinarith
  apply abs_le.mpr
  constructor <;> linarith