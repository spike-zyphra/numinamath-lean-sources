import Mathlib

open BigOperators Real Set

theorem algebra_323450 {f : ℝ → ℝ} (hf : ∃ a b c, a > 0 ∧ ∀ x, f x = a * x ^ 2 + b * x + c)
  (h : ∀ x, f (5 - x) = f (5 + x)) :
  f (2 * π) < f (sqrt 40) ∧ f (sqrt 40) < f (5 * sin (π / 4)) := by
  rcases hf with ⟨a, b, c, ha, h₀⟩
  have h5 : b = -10 * a := by
    have h_eq : ∀ x, f (5 - x) = f (5 + x) := h
    have eq1 := h_eq 1
    have eq2 := h_eq 2
    simp [h₀] at eq1 eq2
    nlinarith
  have h6 : ∀ x₁ x₂ : ℝ, f x₁ < f x₂ ↔ |x₁ - 5| < |x₂ - 5| := by
    intro x₁ x₂
    constructor
    · -- Assume f x₁ < f x₂, prove |x₁ - 5| < |x₂ - 5|
      intro h
      have h5' : b = -10 * a := h5
      have hfx₁ : f x₁ = a * (x₁ - 5) ^ 2 + (c - 25 * a) := by
        rw [h₀ x₁]
        have : b = -10 * a := h5
        rw [this]
        ring_nf
      have hfx₂ : f x₂ = a * (x₂ - 5) ^ 2 + (c - 25 * a) := by
        rw [h₀ x₂]
        have : b = -10 * a := h5
        rw [this]
        ring_nf
      rw [hfx₁] at h
      rw [hfx₂] at h
      have h7 : (x₁ - 5) ^ 2 < (x₂ - 5) ^ 2 := by
        nlinarith
      have h9 : |x₁ - 5| < |x₂ - 5| := by
        apply sq_lt_sq.mp
        exact h7
      exact h9
    · -- Assume |x₁ - 5| < |x₂ - 5|, prove f x₁ < f x₂
      intro h
      have h5' : b = -10 * a := h5
      have hfx₁ : f x₁ = a * (x₁ - 5) ^ 2 + (c - 25 * a) := by
        rw [h₀ x₁]
        have : b = -10 * a := h5
        rw [this]
        ring_nf
      have hfx₂ : f x₂ = a * (x₂ - 5) ^ 2 + (c - 25 * a) := by
        rw [h₀ x₂]
        have : b = -10 * a := h5
        rw [this]
        ring_nf
      have h10 : (x₁ - 5) ^ 2 < (x₂ - 5) ^ 2 := by
        apply sq_lt_sq.mpr
        exact h
      rw [hfx₁, hfx₂]
      nlinarith
  have h7 : f (2 * π) < f (sqrt 40) := by
    have h8 : |(2 * π) - 5| < |sqrt 40 - 5| := by
      have h113 : sqrt 40 > (6 : ℝ) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (40 : ℝ) by norm_num), Real.sqrt_nonneg 40]
      have h114 : (2 * π - 5 : ℝ) > 0 := by
        nlinarith [Real.pi_gt_three]
      have h115 : (sqrt 40 - 5 : ℝ) > 0 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (40 : ℝ) by norm_num), Real.sqrt_nonneg 40]
      have h117 : |(2 * π) - 5| = (2 * π - 5 : ℝ) := by
        apply abs_of_pos
        nlinarith [Real.pi_gt_three]
      have h118 : |sqrt 40 - 5| = (sqrt 40 - 5 : ℝ) := by
        apply abs_of_pos
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (40 : ℝ) by norm_num), Real.sqrt_nonneg 40]
      rw [h117, h118]
      nlinarith [Real.pi_lt_31416, Real.sq_sqrt (show (0 : ℝ) ≤ (40 : ℝ) by norm_num)]
    have h13 : f (2 * π) < f (sqrt 40) := by
      have h14 : |(2 * π) - 5| < |sqrt 40 - 5| := h8
      have h15 : f (2 * π) < f (sqrt 40) := by
        apply (h6 (2 * π) (sqrt 40)).mpr
        exact h8
      exact h15
    exact h13
  have h80 : f (sqrt 40) < f (5 * sin (π / 4)) := by
    have h81 : |sqrt 40 - 5| < |5 * sin (π / 4) - 5| := by
      have h113 : sqrt 40 > (6 : ℝ) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (40 : ℝ) by norm_num), Real.sqrt_nonneg 40]
      have h114 : (sqrt 40 - 5 : ℝ) > 0 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (40 : ℝ) by norm_num), Real.sqrt_nonneg 40]
      have h115 : (5 * sin (π / 4) - 5 : ℝ) < 0 := by
        have h116 : sin (π / 4) = Real.sqrt 2 / 2 := by
          rw [sin_pi_div_four]
        rw [h116]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ 2)]
      have h117 : |sqrt 40 - 5| = (sqrt 40 - 5 : ℝ) := by
        apply abs_of_pos
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (40 : ℝ) by norm_num), Real.sqrt_nonneg 40]
      have h118 : |5 * sin (π / 4) - 5| = - (5 * sin (π / 4) - 5) := by
        apply abs_of_neg
        linarith
      rw [h117, h118]
      have h119 : sin (π / 4) = Real.sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      rw [h119]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 40 by norm_num : (0 : ℝ) < 40), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (40 : ℝ) by norm_num : (0 : ℝ) ≤ 40)]
    have h120 : f (sqrt 40) < f (5 * sin (π / 4)) := by
      have h143 : |sqrt 40 - 5| < |5 * sin (π / 4) - 5| := h81
      have h144 : f (sqrt 40) < f (5 * sin (π / 4)) := by
        apply (h6 (sqrt 40) (5 * sin (π / 4))).mpr
        exact h81
      exact h144
    exact h120
  constructor
  · exact h7
  · exact h80