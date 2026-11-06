import Mathlib

open Real Int Nat

theorem algebra_9306 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x)
    (h₁ : ∀ x, f (x + Real.pi) = f x) (h₂ : ∀ x ∈ Set.Icc 0 (Real.pi / 2), f x = Real.pi / 2 - x) :
    f (5 * Real.pi / 3) = Real.pi / 6 := by

  have h3 : f (5 * Real.pi / 3) = f (2 * Real.pi / 3) := by
    have h4 : 5 * Real.pi / 3 = 2 * Real.pi / 3 + Real.pi := by
      linarith
    rw [h4]
    rw [show f (2 * Real.pi / 3 + Real.pi) = f (2 * Real.pi / 3) by
      rw [h₁]
      all_goals
        ring_nf
    ]
  have h4 : f (2 * Real.pi / 3) = f (- (Real.pi / 3)) := by
    have h5 : 2 * Real.pi / 3 = - (Real.pi / 3) + Real.pi := by
      linarith
    rw [h5]
    have h6 : f (- (Real.pi / 3) + Real.pi) = f (- (Real.pi / 3)) := by
      rw [show - (Real.pi / 3) + Real.pi = (- (Real.pi / 3)) + Real.pi by ring]
      rw [h₁]
    rw [h6]

  have h5 : f (- (Real.pi / 3)) = f (Real.pi / 3) := by
    apply h₀

  have h6 : Real.pi / 3 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · -- Show 0 ≤ π/3
      linarith [Real.pi_pos]
    · -- Show π/3 ≤ π/2
      linarith [Real.pi_pos]

  have h7 : f (Real.pi / 3) = Real.pi / 2 - (Real.pi / 3) := by
    apply h₂
    exact h6

  rw [h3, h4, h5, h7]
  all_goals ring_nf