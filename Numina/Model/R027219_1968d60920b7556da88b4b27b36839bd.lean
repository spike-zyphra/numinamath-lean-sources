import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_114260 (a b c : ℝ)
  (h : ∀ x : ℝ, a * cos x + b * cos (2 * x) + c * cos (3 * x) ≥ -1) :
  a + b + c ≤ 3 := by
  have h1 := h 0
  have h2 := h (Real.pi)
  have h3 := h (Real.pi / 2)
  have h4 := h (Real.pi / 3)
  have h5 := h (2 * Real.pi / 3)
  have h1' : a * cos (0 : ℝ) + b * cos (2 * (0 : ℝ)) + c * cos (3 * (0 : ℝ)) ≥ -1 := by
    simpa using h1
  have h2' : a * cos Real.pi + b * cos (2 * Real.pi) + c * cos (3 * Real.pi) ≥ -1 := by 
    simpa using h2
  have h3' : a * cos (Real.pi / 2) + b * cos (2 * (Real.pi / 2)) + c * cos (3 * (Real.pi / 2)) ≥ -1 := by 
    simpa using h3
  have h4' : a * cos (Real.pi / 3) + b * cos (2 * (Real.pi / 3)) + c * cos (3 * (Real.pi / 3)) ≥ -1 := by 
    simpa using h4
  have h5' : a * cos (2 * Real.pi / 3) + b * cos (2 * (2 * Real.pi / 3)) + c * cos (3 * (2 * Real.pi / 3)) ≥ -1 := by 
    simpa using h5
  have h7 : cos (0 : ℝ) = 1 := by 
    exact cos_zero
  have h8 : cos (2 * (0 : ℝ)) = 1 := by 
    simp [show (2 * (0 : ℝ) : ℝ) = (0 : ℝ) by ring]
  have h9 : cos (3 * (0 : ℝ)) = 1 := by 
    simp [show (3 * (0 : ℝ) : ℝ) = (0 : ℝ) by ring]
  have h10 : cos Real.pi = -1 := Real.cos_pi
  have h11 : cos (2 * Real.pi) = 1 := by 
    exact Real.cos_two_pi
  have h12 : cos (3 * Real.pi) = -1 := by 
    have h1 : 3 * Real.pi = Real.pi + 2 * Real.pi := by 
      nlinarith [Real.pi_pos]
    rw [h1]
    rw [cos_add, cos_two_pi, sin_two_pi]
    all_goals norm_num
  have h13 : cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have h14 : cos (2 * (Real.pi / 2)) = -1 := by
    have h1 : 2 * (Real.pi / 2) = Real.pi := by 
      ring_nf
    rw [h1]
    linarith [Real.cos_pi]
  have h15 : cos (3 * (Real.pi / 2)) = 0 := by 
    have h1 : 3 * (Real.pi / 2) = Real.pi / 2 + Real.pi := by 
      ring_nf
    rw [h1]
    rw [cos_add, cos_pi, sin_pi]
    norm_num
  have h16 : cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have h17 : cos (2 * (Real.pi / 3)) = -1 / 2 := by
    have h1 : 2 * (Real.pi / 3) = 2 * Real.pi / 3 := by ring
    rw [h1]
    have h2 : cos (2 * Real.pi / 3) = -1 / 2 := by 
      have h3 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by linarith [Real.pi_pos]
      rw [h3]
      rw [cos_pi_sub]
      linarith [Real.cos_pi_div_three]
    linarith
  have h18 : cos (3 * (Real.pi / 3)) = -1 := by
    have h1 : 3 * (Real.pi / 3) = Real.pi := by 
      ring_nf
    rw [h1]
    linarith [Real.cos_pi]
  have h19 : cos (2 * Real.pi / 3) = -1 / 2 := by
    have h1 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by linarith [Real.pi_pos]
    rw [h1]
    rw [cos_pi_sub]
    linarith [Real.cos_pi_div_three]
  have h20 : cos (2 * (2 * Real.pi / 3)) = -1 / 2 := by 
    have h1 : 2 * (2 * Real.pi / 3) = 4 * Real.pi / 3 := by 
      ring_nf
    rw [h1]
    have h2 : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 := by 
      nlinarith [Real.pi_pos]
    rw [h2]
    rw [cos_add, cos_pi, sin_pi]
    all_goals norm_num [Real.cos_pi_div_three, Real.sin_pi_div_three]
  have h21 : cos (3 * (2 * Real.pi / 3)) = 1 := by
    have h1 : 3 * (2 * Real.pi / 3) = 2 * Real.pi := by 
      ring_nf
    rw [h1]
    linarith [Real.cos_two_pi]
  simp only [h7, h8, h9] at h1'
  simp only [h10, h11, h12] at h2'
  simp only [h13, h14, h15] at h3'
  simp only [h16, h17, h18] at h4'
  simp only [h19, h20, h21] at h5'
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 2), 
            Real.sin_sq_add_cos_sq 0, Real.sin_sq_add_cos_sq Real.pi, 
            Real.sin_sq_add_cos_sq (Real.pi / 2), 
            Real.sin_sq_add_cos_sq (Real.pi / 3), 
            Real.sin_sq_add_cos_sq (2 * Real.pi / 3), 
            sq_nonneg (a + b + c - 3), 
            sq_nonneg (a - c), sq_nonneg (b - 1)]