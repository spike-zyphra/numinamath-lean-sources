import Mathlib

open Real Set
open scoped Real

theorem calculus_23329{sec: ℝ → ℝ}(hsec: ∀α:ℝ, sec α = 1 / (cos α)) :
  IsLeast {x : ℝ | ∃ α β, x = (sec α)^4 / (tan β)^2 + (sec β)^4 / (tan α)^2 ∧ cos α ≠ 0 ∧ cos β ≠ 0 ∧ tan α ≠ 0 ∧ tan β ≠ 0} 8 := by
  constructor
  · -- Show 8 is achievable using α = β = π / 4
    use Real.pi / 4, Real.pi / 4
    constructor
    · -- Show the value equals 8 at π / 4
      have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        apply Real.sin_pi_div_four
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        apply Real.cos_pi_div_four
      have htan : tan (Real.pi / 4) = 1 := by
        rw [Real.tan_eq_sin_div_cos, h1, h2]
        field_simp
      have hsec_val : (sec (Real.pi / 4)) ^ 4 / (tan (Real.pi / 4)) ^ 2 + (sec (Real.pi / 4)) ^ 4 / (tan (Real.pi / 4)) ^ 2 = 8 := by
        have htan_val : tan (Real.pi / 4) = 1 := htan
        have hsec_val : sec (Real.pi / 4) = Real.sqrt 2 := by
          rw [hsec]
          have hcos : cos (Real.pi / 4) = Real.sqrt 2 / 2 := h2
          rw [hcos]
          field_simp
          <;> ring_nf <;> field_simp
        rw [hsec_val, htan_val]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith [hsec_val]
    constructor
    · -- Show cos (π/4) ≠ 0
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      have hne : cos (Real.pi / 4) ≠ 0 := by
        rw [h2]
        linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      exact hne
    constructor
    · -- Show cos (π/4) ≠ 0
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      have hne : cos (Real.pi / 4) ≠ 0 := by
        rw [h2]
        linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      exact hne
    constructor
    · -- Show tan (π/4) ≠ 0
      have htan : tan (Real.pi / 4) = 1 := by
        rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_four, Real.cos_pi_div_four]
        field_simp
      have hne : tan (Real.pi / 4) ≠ 0 := by
        rw [htan]
        norm_num
      exact hne
    · -- Show tan (π/4) ≠ 0
      have htan : tan (Real.pi / 4) = 1 := by
        rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_four, Real.cos_pi_div_four]
        field_simp
      have hne : tan (Real.pi / 4) ≠ 0 := by
        rw [htan]
        norm_num
      exact hne

  · -- Show 8 is a lower bound
    rintro x ⟨α, β, hx_eq, ha, hb, ha't, hb't⟩
    have h1 : x ≥ 8 := by
      rw [hx_eq]
      -- Rewrite in terms of tan α and tan β
      have hsecα : (sec α) ^ 4 / (tan β) ^ 2 + (sec β) ^ 4 / (tan α) ^ 2 = (1 + (tan α)^2)^2 / (tan β)^2 + (1 + (tan β)^2)^2 / (tan α)^2 := by
        have htanα : tan α = sin α / cos α := by
          rw [Real.tan_eq_sin_div_cos]
        have htanβ : tan β = sin β / cos β := by
          rw [Real.tan_eq_sin_div_cos]
        rw [hsec α, hsec β]
        have h1 : (1 / (cos α)) ^ 4 / (tan β) ^ 2 = (1 + (tan α)^2) ^ 2 / (tan β)^2 := by
          rw [htanα]
          field_simp [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero ha't, sq_pos_of_ne_zero hb't, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
          <;> nlinarith [sq_nonneg (sin α), sq_nonneg (sin β), sq_nonneg (cos α - cos β), sq_nonneg (sin α * cos β - sin β * cos α)]
        have h2 : (1 / (cos β)) ^ 4 / (tan α)^2 = (1 + (tan β)^2) ^ 2 / (tan α)^2 := by
          rw [htanβ]
          field_simp [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero ha't, sq_pos_of_ne_zero hb't, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
          <;> nlinarith [sq_nonneg (sin α), sq_nonneg (sin β), sq_nonneg (cos α - cos β), sq_nonneg (sin α * cos β - sin β * cos α)]
        linarith [h1, h2]
      rw [hsecα]
      have h2 : (1 + (tan α)^2)^2 / (tan β)^2 + (1 + (tan β)^2)^2 / (tan α)^2 ≥ 8 := by
        have h2a : (tan α) ^ 2 > 0 := by
          have htanαne' : tan α ≠ 0 := ha't
          have h1 : (tan α) ^ 2 > 0 := by
            apply sq_pos_of_ne_zero
            exact htanαne'
          exact h1
        have h2b : (tan β) ^ 2 > 0 := by
          have htanβne' : tan β ≠ 0 := hb't
          have h1 : (tan β) ^ 2 > 0 := by
            apply sq_pos_of_ne_zero
            exact htanβne'
          exact h1
        have h4 : (1 + (tan α)^2) ^ 2 / (tan β)^2 + (1 + (tan β)^2) ^ 2 / (tan α)^2 - 8 ≥ 0 := by
          have h5 : 0 < (tan α)^2 * (tan β)^2 := by positivity
          have eq : (1 + (tan α)^2) ^ 2 / (tan β)^2 + (1 + (tan β)^2) ^ 2 / (tan α)^2 - 8 =
            ((1 + (tan α)^2) ^ 2 * (tan α)^2 + (1 + (tan β)^2) ^ 2 * (tan β)^2 - 8 * (tan α)^2 * (tan β)^2) / ((tan α)^2 * (tan β)^2) := by
            field_simp
            ring
          rw [eq]
          apply div_nonneg
          -- Show the numerator is nonnegative
          nlinarith [sq_nonneg ((1 + (tan α)^2) * (tan α) - (1 + (tan β)^2) * (tan β)), sq_nonneg ((1 + (tan α)^2) * (tan β) - (1 + (tan β)^2) * (tan α)), sq_nonneg ((tan α)^2 - (tan β)^2), sq_nonneg ((tan α)^2 - 1), sq_nonneg ((tan β)^2 - 1)]
          -- Show the denominator is positive
          positivity
        linarith
      linarith
    linarith