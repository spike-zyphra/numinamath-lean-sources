import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_146706 {f : ℝ → ℝ}
  (h : ∀ x ∈ Icc 0 Real.pi, f (cos x) = x / 2) :
  f (-1 / 2) = Real.pi / 3 := by
  have h1 : cos (2 * Real.pi / 3) = -1 / 2 := by
    have h2 : cos (2 * Real.pi / 3) = -cos (Real.pi / 3) := by 
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
      rw [cos_pi_sub]
    rw [h2]
    rw [cos_pi_div_three]
    norm_num
  have h2 : 2 * Real.pi / 3 ∈ Icc 0 Real.pi := by 
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have h3 := h (2 * Real.pi / 3) h2
  rw [h1] at h3
  have h4 : f (-1 / 2) = Real.pi / 3 := by 
    linarith
  exact h4