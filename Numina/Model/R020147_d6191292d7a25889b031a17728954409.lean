import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_325457 {a b : ℝ} (h : ∀ x : ℝ, a * cos x + b * cos (3 * x) ≤ 1) :
    |b| ≤ 1 := by 
  have h1 := h 0
  have h1' : a * Real.cos (0 : ℝ) + b * Real.cos (3 * (0 : ℝ)) ≤ 1 := h1
  have h2 := h (Real.pi)
  have h2' : a * Real.cos Real.pi + b * Real.cos (3 * Real.pi) ≤ 1 := h2
  have h3 := h (Real.pi / 3)
  have h3' : a * Real.cos (Real.pi / 3) + b * Real.cos (3 * (Real.pi / 3)) ≤ 1 := h3
  have h4 := h (2 * Real.pi / 3)
  have h4' : a * Real.cos (2 * Real.pi / 3) + b * Real.cos (3 * (2 * Real.pi / 3)) ≤ 1 := h4
  have hcos1 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
  have hcos2 : Real.cos (Real.pi : ℝ) = -1 := by
    exact Real.cos_pi
  have hcos3 : Real.cos (3 * (0 : ℝ)) = 1 := by
    have h1 : (3 * (0 : ℝ) : ℝ) = 0 := by
      ring_nf
    rw [h1]
    exact Real.cos_zero
  have hcos4 : Real.cos (3 * Real.pi) = -1 := by
    have h1 : (3 * Real.pi : ℝ) = Real.pi + 2 * Real.pi := by
      linarith [Real.pi_pos]
    rw [h1]
    have h2 : Real.cos (Real.pi + 2 * Real.pi) = Real.cos (Real.pi) := by
      rw [Real.cos_add_two_pi]
    rw [h2, Real.cos_pi]
  have hcos5 : Real.cos (Real.pi / 3) = 1 / 2 := by
    exact Real.cos_pi_div_three
  have hcos6 : Real.cos (3 * (Real.pi / 3)) = -1 := by
    have h1 : 3 * (Real.pi / 3) = Real.pi := by
      ring_nf
    rw [h1]
    exact Real.cos_pi
  have hcos7 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have h1 : 2 * Real.pi / 3 = Real.pi - (Real.pi / 3) := by
      ring_nf
    rw [h1]
    have h2 : Real.cos (Real.pi - (Real.pi / 3)) = - Real.cos (Real.pi / 3) := by
      rw [Real.cos_pi_sub]
    rw [h2, Real.cos_pi_div_three]
    all_goals norm_num
  have hcos8 : Real.cos (3 * (2 * Real.pi / 3)) = 1 := by
    have h1 : 3 * (2 * Real.pi / 3) = 2 * Real.pi := by
      ring_nf
    rw [h1]
    exact Real.cos_two_pi
  simp [hcos1, hcos3] at h1'
  simp [hcos2, hcos4] at h2'
  simp [hcos5, hcos6] at h3'
  simp [hcos7, hcos8] at h4'
  have h5 : -1 ≤ b := by
    linarith [h1', h2', h3', h4']
  have h6 : b ≤ 1 := by
    linarith [h1', h2', h3', h4']
  apply abs_le.mpr
  constructor <;> linarith