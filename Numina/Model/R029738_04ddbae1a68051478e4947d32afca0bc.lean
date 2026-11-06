import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_221879 (a b : ℝ) :
  {x : ℝ | a * cos x + b * cos (3 * x) > 1} = ∅ → |b| ≤ 1 := by
  intro h
  have h1 : ∀ x : ℝ, ¬ (a * cos x + b * cos (3 * x) > 1) := by
    intro x
    have hx : x ∉ {x : ℝ | a * cos x + b * cos (3 * x) > 1} := by
      rw [h]
      simp
    simp at hx ⊢
    tauto
  have h2 := h1 0
  have h3 : a * cos (0 : ℝ) + b * cos (3 * (0 : ℝ)) ≤ (1 : ℝ) := by
    linarith [h2]
  have h4 : cos (0 : ℝ) = 1 := by
    simp
  have h5 : cos (3 * (0 : ℝ)) = 1 := by
    simp [show 3 * (0 : ℝ) = (0 : ℝ) by ring]
  rw [h4, h5] at h3
  have h6 : a + b ≤ 1 := by
    linarith
  have h7 := h1 (Real.pi)
  have h8 : a * cos (Real.pi) + b * cos (3 * Real.pi) ≤ (1 : ℝ) := by
    linarith [h7]
  have h9 : cos (Real.pi) = -1 := by
    exact Real.cos_pi
  have h10 : cos (3 * Real.pi) = -1 := by
    have h11 : 3 * Real.pi = 2 * Real.pi + Real.pi := by
      ring_nf
    rw [h11]
    have h12 : cos (2 * Real.pi + Real.pi) = cos (Real.pi) := by
      rw [cos_add, cos_two_pi, sin_two_pi]
      norm_num
    rw [h12, Real.cos_pi]
  rw [h9, h10] at h8
  have h13 : a + b ≥ -1 := by
    linarith
  have h8 := h1 (Real.pi / 3)
  have h9 : a * cos (Real.pi / 3) + b * cos (3 * (Real.pi / 3)) ≤ (1 : ℝ) := by
    linarith [h8]
  have h10 : cos (Real.pi / 3) = 1 / 2 := by
    exact Real.cos_pi_div_three
  have h11 : cos (3 * (Real.pi / 3)) = -1 := by
    have : 3 * (Real.pi / 3) = Real.pi := by
      ring
    rw [this]
    exact Real.cos_pi
  rw [h10, h11] at h9
  have h14 := h1 (2 * Real.pi / 3)
  have h15 : a * cos (2 * Real.pi / 3) + b * cos (3 * (2 * Real.pi / 3)) ≤ (1 : ℝ) := by
    linarith [h14
    ]
  have h16 : cos (2 * Real.pi / 3) = -1 / 2 := by
    have h1 : 2 * Real.pi / 3 = Real.pi - (Real.pi / 3) := by
      ring_nf
    rw [h1]
    have h2 : cos (Real.pi - (Real.pi / 3)) = -cos (Real.pi / 3) := by
      rw [cos_pi_sub]
    rw [h2, Real.cos_pi_div_three]
    all_goals norm_num
  have h17 : cos (3 * (2 * Real.pi / 3)) = 1 := by
    have : 3 * (2 * Real.pi / 3) = 2 * Real.pi := by
      ring_nf
    rw [this]
    exact Real.cos_two_pi
  rw [h16, h17] at h15
  have h18 : -1 ≤ b ∧ b ≤ 1 := by
    constructor
    · -- Show that -1 <= b
      linarith
    · -- Show that b <= 1
      linarith
  apply abs_le.mpr
  constructor <;> linarith [h18.1, h18.2]