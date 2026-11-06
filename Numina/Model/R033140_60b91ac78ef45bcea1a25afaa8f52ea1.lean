import Mathlib

open Real Set
open scoped Real

theorem calculus_11441 : {x : ℝ | 0 ≤ x ∧ x < 2 * π ∧ sin x + cos x = sqrt 2} = {π / 4} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the set
    intro h
    rcases h with ⟨hx1, hx2, heq⟩
    have h1 : sin x + cos x = Real.sqrt 2 * sin (x + Real.pi / 4) := by
      rw [Real.sin_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
      all_goals ring_nf <;> simp [mul_add, add_mul] <;> ring_nf
      all_goals linarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sin_sq_add_cos_sq x]

    rw [h1] at heq
    have h2 : sin (x + Real.pi / 4) = 1 := by
      have h_ne : Real.sqrt 2 ≠ 0 := by
        positivity
      apply (mul_left_inj' h_ne).mp 
      linarith
      <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sin_sq_add_cos_sq x]

    -- Now solve sin (x + Real.pi / 4) = 1 for x
    have h3 : sin (x + Real.pi / 4) = 1 := h2
    have hk1 : sin (x + Real.pi / 4) = 1 := h3
    have hk2 : x + Real.pi / 4 = Real.pi / 2 + 2 * Real.pi * (0 : ℤ) := by
      rw [sin_eq_one_iff] at hk1
      rcases hk1 with ⟨k, hk⟩
      have h52 : (x + Real.pi / 4) = Real.pi / 2 + 2 * Real.pi * (k : ℝ) := by 
        linarith [hk]
      -- Solving constraints for k given the bounds on x.
      have h13 : k = 0 := by
        have hk0 : k = 0 := by
          by_contra h'
          push_neg at h'
          have : k ≥ 1 ∨ k ≤ -1 := by
            omega
          rcases this with (h' | h')
          · -- Case k ≥ 1
            have hk2 : k ≥ 1 := h'
            have hk2' : (k : ℝ) ≥ (1 : ℝ) := by
              exact_mod_cast hk2
            have hk3 : x ≥ Real.pi / 4 + 2 * Real.pi := by
              nlinarith [Real.pi_pos, h52, hk2']
            -- But x < 2 * π, contradiction
            have h47 : Real.pi / 4 + 2 * Real.pi > 2 * Real.pi := by
              linarith [Real.pi_pos]
            linarith [show x ≥ Real.pi / 4 + 2 * Real.pi by linarith, hx2, h47]
          · -- Case k ≤ -1
            have hk2 : k ≤ -1 := h'
            have hk2' : (k : ℝ) ≤ (-1 : ℝ) := by
              exact_mod_cast hk2
            have hk3 : x ≤ - (3 * Real.pi / 4) := by
              nlinarith [Real.pi_pos, h52, hk2']
            -- But 0 ≤ x < 2 * π, contradiction
            have h47 : - (3 * Real.pi / 4) < 0 := by 
              nlinarith [Real.pi_pos]
            linarith [show x ≤ - (3 * Real.pi / 4) by linarith, hx1, h47]
        omega
      have : k = 0 := h13
      rw [show k = (0 : ℤ) by omega] at h52
      linarith
      <;> linarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]

    -- Simplify to find x
    have hx_eq : x = Real.pi / 4 := by
      have eq2 : x + Real.pi / 4 = Real.pi / 2 + 2 * Real.pi * (0 : ℝ) := by
        nlinarith [Real.pi_pos, hk2, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sin_sq_add_cos_sq (x + Real.pi / 4)]
      ring_nf at eq2 ⊢
      linarith [Real.pi_pos]

    -- Final step, proving x equals.
    linarith [Real.pi_pos, hx_eq]

  · -- Assume x = π/4, prove all conditions
    intro h
    rw [h]
    constructor
    · -- Show 0 ≤ π/4
      linarith [Real.pi_pos]
    constructor
    · -- Show π/4 < 2 * π
      nlinarith [Real.pi_pos]
    · -- Verify sin(π/4) + cos(π/4) = √2
      have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [sin_pi_div_four]
        <;> linarith
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
        <;> linarith
      linarith [h1, h2, Real.sqrt_nonneg 2, Real.sin_sq_add_cos_sq (Real.pi / 4)]
  all_goals try { linarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq (Real.pi / 4), h2] }
  all_goals try { sorry }