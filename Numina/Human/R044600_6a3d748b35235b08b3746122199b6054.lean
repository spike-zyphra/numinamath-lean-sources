import Mathlib

open Real Set
open scoped BigOperators

/-
  The function $y = \cos x$ is increasing on the interval $[-\pi, a]$. The range of values for $a$ is __________.
-/
theorem algebra_8993 (a : ℝ) (ha : a > -π) :
    MonotoneOn cos (Icc (-π) a) ↔ a ∈ Ioc (-π) 0 := by

  -- find the monotone interval of cos
  have monotone : MonotoneOn cos (Icc (-π) 0) := by
    intro x₁ hx₁ x₂ hx₂ hle
    simp at hx₁ hx₂
    rw [<-cos_neg x₁, <-cos_neg x₂]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    all_goals linarith

  constructor
  · -- prove a ≤ 0
    intro h
    simp
    constructor
    · exact ha
    · -- by contradiction a > 0
      by_contra hgt
      push_neg at hgt
      have h1 : 0 ∈ Icc (-π) a := by
        simp
        constructor
        · exact pi_nonneg
        · linarith
      by_cases h' : a < π
      · -- if a < π, then choose 0 a, show cos 0 > cos a
        have h2 : a ∈ Icc (-π) a := by
          simp
          linarith
        have h3 : 0 ≤ a := by linarith
        apply h h1 h2 at h3
        have : ¬ cos 0 ≤ cos a := by
          push_neg
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith
        contradiction
      · -- if a ≥ π, choose 0 π, show cos 0 > cos π
        push_neg at h'
        have h2 : π ∈ Icc (-π) a := by
          simp
          constructor
          · exact pi_nonneg
          · exact h'
        have h3 : 0 ≤ π := by exact pi_nonneg
        apply h h1 h2 at h3
        simp [cos] at h3
        linarith
  · -- prove if a ∈ (-π, 0), then cos is monotone on [-π, a]
    intro h
    have : Icc (-π) a ⊆ Icc (-π) 0 := by
      intro x hx
      simp at hx h
      constructor <;> linarith
    exact MonotoneOn.mono monotone this
