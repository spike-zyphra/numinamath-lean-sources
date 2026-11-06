import Mathlib

open Real Set
open scoped Real

theorem algebra_12971 : IsLeast {x | ∃ t, x = sin t ∧ tan t - 2 / tan t = 1} (-2 * sqrt 5 / 5) := by
  constructor
  · -- Show that -2 * sqrt(5) / 5 is in the set.
    use Real.pi + Real.arcsin (2 * Real.sqrt 5 / 5)
    have h1 : Real.sin (Real.pi + Real.arcsin (2 * Real.sqrt 5 / 5)) = -Real.sin (Real.arcsin (2 * Real.sqrt 5 / 5)) := by
      rw [Real.sin_add, Real.sin_pi, Real.cos_pi]
      ring
    have h2 : Real.sin (Real.arcsin (2 * Real.sqrt 5 / 5)) = 2 * Real.sqrt 5 / 5 := by
      apply Real.sin_arcsin
      · -- Show 2 * sqrt 5 / 5 ≥ -1
        nlinarith [Real.sqrt_pos.mpr (show (5: ℝ) > 0 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (5: ℝ) by norm_num)]
      · -- Show 2 * sqrt 5 / 5 ≤ 1
        nlinarith [Real.sqrt_pos.mpr (show (5: ℝ) > 0 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (5: ℝ) by norm_num)]
    have h3 : Real.sin (Real.pi + Real.arcsin (2 * Real.sqrt 5 / 5)) = -2 * Real.sqrt 5 / 5 := by
      rw [h1, h2]
      <;> ring
    -- Calculate cos t
    have h4 : Real.cos (Real.pi + Real.arcsin (2 * Real.sqrt 5 / 5)) = - Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5)) := by
      rw [Real.cos_add, Real.sin_pi, Real.cos_pi]
      ring
    -- Calculate cos (arcsin (2 * sqrt 5 / 5))
    have h5 : Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5)) = Real.sqrt 5 / 5 := by
      have h71 : Real.sin (Real.arcsin (2 * Real.sqrt 5 / 5)) = 2 * Real.sqrt 5 / 5 := h2
      have h72 : (Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5))) ^ 2 + (Real.sin (Real.arcsin (2 * Real.sqrt 5 / 5))) ^ 2 = 1 := by
        have h74 : (Real.sin (Real.arcsin (2 * Real.sqrt 5 / 5))) ^ 2 + (Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5))) ^ 2 = 1 := by
          have h75 : Real.sin (Real.arcsin (2 * Real.sqrt 5 / 5)) ^ 2 + Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5)) ^ 2 = 1 := by
            have h76 : Real.sin (Real.arcsin (2 * Real.sqrt 5 / 5)) ^ 2 + Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5)) ^ 2 = 1 := by
              rw [Real.sin_sq_add_cos_sq (Real.arcsin (2 * Real.sqrt 5 / 5))]
            linarith [h76]
          linarith [h75]
        linarith [h74]
      rw [h71] at h72
      -- Now find expressions for cos^2
      have h73 : (Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5)))^2 = 1/5 := by
        nlinarith [h72, Real.sqrt_pos.mpr (show (5: ℝ) > 0 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (5: ℝ) by norm_num)]
      have h30 : 0 ≤ Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5)) := by
        apply Real.cos_arcsin_nonneg
        all_goals
          nlinarith [Real.sqrt_pos.mpr (show (5: ℝ) > 0 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (5: ℝ) by norm_num)]
      -- Solve for cos
      have h74 : Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5)) = Real.sqrt (1 / 5) := by
        have h75 : Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5)) ≥ 0 := h30
        have h85 : (Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5))) ^ 2 = (1 / (5 : ℝ)) := h73
        have h86 : Real.cos (Real.arcsin (2 * Real.sqrt 5 / 5)) = Real.sqrt (1 / (5 : ℝ)) := by
          rw [← h85]
          field_simp [h75, Real.sqrt_nonneg]
          <;> nlinarith [h75, Real.sqrt_nonneg (1 / (5 : ℝ)), Real.sqrt_nonneg (1 / (5 : ℝ))]
        exact h86
      rw [h74]
      have h87 : Real.sqrt (1 / (5 : ℝ)) = Real.sqrt 5 / 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [h87]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    -- Calculate cos t
    have h6 : Real.cos (Real.pi + Real.arcsin (2 * Real.sqrt 5 / 5)) = - Real.sqrt 5 / 5 := by
      rw [h4, h5]
      <;> ring
    -- Calculate tan t
    have htan : tan (Real.pi + Real.arcsin (2 * Real.sqrt 5 / 5)) = 2 := by
      rw [tan_eq_sin_div_cos, h3, h6]
      <;> field_simp
      <;> ring_nf <;> norm_num
      all_goals norm_num
    constructor
    · -- Show x = sin t
      linarith [h3]
    · -- Show tan t - 2 / tan t = 1
      rw [htan]
      norm_num
      all_goals norm_num
  · -- Show that -2 * sqrt(5) / 5 is the least
    intro x hx
    rcases hx with ⟨t, ht_eq, ht_eq1⟩
    have ht1 : sin t ≠ 0 := by
      by_contra h
      have htan0 : tan t = 0 := by
        rw [tan_eq_sin_div_cos]
        simp [h]
      rw [htan0] at ht_eq1
      norm_num at ht_eq1
      all_goals norm_num at ht_eq1
    have ht2 : cos t ≠ 0 := by
      by_contra h
      have htan0 : tan t = 0 := by
        rw [tan_eq_sin_div_cos]
        simp [h]
      rw [htan0] at ht_eq1
      norm_num at ht_eq1
      all_goals norm_num at ht_eq1
    have ht3 : (sin t) ^ 2 - 2 * (cos t) ^ 2 = sin t * cos t := by
      have htan_eq : tan t = sin t / cos t := by
        rw [tan_eq_sin_div_cos]
      rw [htan_eq] at ht_eq1
      field_simp [ht1, ht2] at ht_eq1 ⊢
      nlinarith [ht_eq1]
    have h1 : (cos t) ^ 2 = 1 - (sin t) ^ 2 := by
      have h2 : (sin t) ^ 2 + (cos t) ^ 2 = 1 := Real.sin_sq_add_cos_sq t
      linarith [h2]
    rw [h1] at ht3
    nlinarith [sq_nonneg ( (sin t) ^ 2 - 4 / 5 ), sq_nonneg ( (sin t) ^ 2 - 1 / 2 ), sq_nonneg ( sin t - (-2 * Real.sqrt 5 / 5) ), sq_nonneg ( sin t ), sq_nonneg ( sin t * cos t ), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num) ]