import Mathlib

theorem algebra_275744 (P Q R S : ℝ × ℝ)
    (hP : P = (2, 1)) (hR : R = (P + Q) / 2) (hS : S = (Q + R) / 2)
    (hS1 : S = (14, 7)) : Q = (18, 9) := by
  rw [hP] at hR
  simp [Prod.ext_iff] at hR hS hS1 ⊢
  norm_num at hR hS hS1 ⊢
  constructor
  · -- Solving for x-coordinate
    linarith
  · -- Solving for y-coordinate
    linarith