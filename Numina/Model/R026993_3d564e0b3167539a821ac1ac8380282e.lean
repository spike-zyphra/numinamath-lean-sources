import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_181492 (f : ℝ → ℝ)
  (hf : f = λ x => sin (2 * x) / sin (π / 4 + x)) :
  IsLeast (image f (Icc 0 (π / 2))) 0 ∧ IsGreatest (image f (Icc 0 (π / 2))) 1 := by
  constructor
  · -- Prove 0 is the least
    constructor
    · -- Show 0 is in the image.
      use 0
      constructor
      · -- Show 0 is in the interval
        exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      · -- Show f(0) = 0
        rw [hf]
        norm_num [sin_two_mul, cos_pi_div_four, sin_pi_div_four]
    · -- Show 0 is indeed the least
      intro y
      rintro ⟨x, hx, hfx⟩
      rw [hf] at hfx
      simp at hfx
      rcases hx with ⟨hx1, hx2⟩
      have hsin1 : sin (2 * x) ≥ 0 := by 
        apply sin_nonneg_of_nonneg_of_le_pi
        · -- Show 0 ≤ 2 * x
          linarith [Real.pi_pos]
        · -- Show 2 * x ≤ π
          linarith [Real.pi_pos]
      have hsin2 : sin (π / 4 + x) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        all_goals
          linarith [Real.pi_pos]
      have h1 : sin (2 * x) / sin (π / 4 + x) ≥ 0 := by
        apply div_nonneg
        · exact hsin1
        · -- Show sin (π / 4 + x) ≥ 0
          linarith [hsin2]
      linarith [h1, hfx]
  · -- Prove 1 is the greatest
    constructor
    · -- Show 1 is in the image
      use Real.pi / 4
      constructor
      · -- Show π/4 is in the interval
        constructor
        · -- Show 0 ≤ π/4
          linarith [Real.pi_pos]
        · -- Show π/4 ≤ π/2
          linarith [Real.pi_pos]
      · -- Show f(π/4) = 1
        rw [hf]
        have h1 : sin (2 * (Real.pi / 4)) = 1 := by
          have h2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
          rw [h2]
          exact sin_pi_div_two
        have h2 : sin (Real.pi / 4 + Real.pi / 4) = 1 := by
          have h3 : Real.pi / 4 + Real.pi / 4 = Real.pi / 2 := by ring
          rw [h3]
          exact sin_pi_div_two
        simp [h1, h2]
    · -- Show 1 is the greatest
      intro y
      rintro ⟨x, hx, hfx⟩
      rw [hf] at hfx
      simp at hfx
      rcases hx with ⟨hx1, hx2⟩
      have h3 : sin (2 * x) ≤ sin (π / 4 + x) := by
        have h4 : sin (2 * x) = 2 * sin x * cos x := by
          rw [sin_two_mul]
        have h5 : sin (π / 4 + x) = sin (Real.pi / 4) * cos x + cos (Real.pi / 4) * sin x := by
          rw [sin_add]
        rw [h4, h5]
        have h6 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
          rw [sin_pi_div_four]
        have h7 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
          rw [cos_pi_div_four]
        rw [h6, h7]
        have h8 : sin x ≥ 0 := by
          apply sin_nonneg_of_nonneg_of_le_pi
          · -- Show 0 ≤ x
            linarith [Real.pi_pos]
          · -- Show x ≤ π
            linarith [Real.pi_pos]
        have h9 : cos x ≥ 0 := by
          apply cos_nonneg_of_mem_Icc
          constructor
          · -- Show -π/2 ≤ x
            linarith [Real.pi_pos]
          · -- Show x ≤ π/2
            linarith [Real.pi_pos]
        nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), sq_nonneg (sin x), sq_nonneg (cos x - sin x), sq_nonneg (cos x), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sin_sq_add_cos_sq x, mul_nonneg h8 h9]
      have hsin2 : sin (π / 4 + x) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        all_goals
          linarith [Real.pi_pos]
      have h8 : sin (2 * x) / sin (π / 4 + x) ≤ 1 := by
        apply (div_le_iff₀ (by linarith)).mpr
        linarith [h3, hsin2]
      linarith [h8, hfx]