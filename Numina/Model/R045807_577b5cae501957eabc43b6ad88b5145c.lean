import Mathlib

open Real Set

theorem calculus_14894 :
    IsLeast {x : ℝ | ∃ α β : ℝ, x = (2 * cos α + 5 * sin β - 8) ^ 2 +
      (2 * sin α + 5 * cos β - 15) ^ 2} 100 := by
  constructor
  · -- Show that 100 is indeed achievable with specific α and β.
    use Real.arccos (8 / 17), Real.arccos (15 / 17)
    have hcosα : cos (Real.arccos (8 / 17)) = (8 / 17 : ℝ) := by
      apply Real.cos_arccos
      all_goals norm_num
    have hsinα : sin (Real.arccos (8 / 17)) = (15 / 17 : ℝ) := by
      have h1 : sin (Real.arccos (8 / 17)) ≥ 0 := by
        apply sin_nonneg_of_nonneg_of_le_pi
        · -- Show 0 ≤ Real.arccos (8 / 17)
          linarith [Real.arccos_nonneg (8 / 17)]
        · -- Show Real.arccos (8 / 17) ≤ π
          linarith [Real.arccos_le_pi (8 / 17)]
      have h2 : sin (Real.arccos (8 / 17)) ^ 2 + cos (Real.arccos (8 / 17)) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (Real.arccos (8 / 17))
      rw [hcosα] at h2
      have h3 : sin (Real.arccos (8 / 17)) ^ 2 = 225 / 289 := by
        nlinarith
      have h4 : sin (Real.arccos (8 / 17)) = 15 / 17 := by
        nlinarith [h1]
      linarith
    have hcosβ : cos (Real.arccos (15 / 17)) = (15 / 17 : ℝ) := by
      apply Real.cos_arccos
      all_goals norm_num
    have hsinβ : sin (Real.arccos (15 / 17)) = (8 / 17 : ℝ) := by
      have h1 : sin (Real.arccos (15 / 17)) ≥ 0 := by
        apply sin_nonneg_of_nonneg_of_le_pi
        · -- Show 0 ≤ Real.arccos (15 / 17)
          linarith [Real.arccos_nonneg (15 / 17)]
        · -- Show Real.arccos (15 / 17) ≤ π
          linarith [Real.arccos_le_pi (15 / 17)]
      have h2 : sin (Real.arccos (15 / 17)) ^ 2 + cos (Real.arccos (15 / 17)) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (Real.arccos (15 / 17))
      rw [hcosβ] at h2
      have h3 : sin (Real.arccos (15 / 17)) ^ 2 = 64 / 289 := by
        nlinarith
      have h4 : sin (Real.arccos (15 / 17)) = 8 / 17 := by
        nlinarith [h1]
      linarith
    rw [hcosα, hsinα, hcosβ, hsinβ]
    norm_num
  · -- Show that 100 is the least element in the set
    intro x hx
    rcases hx with ⟨α, β, h_eq⟩
    have h1 : (2 * cos α + 5 * sin β - 8) ^ 2 + (2 * sin α + 5 * cos β - 15) ^ 2 ≥ 100 := by
      nlinarith [sq_nonneg (2 * cos α + 5 * sin β - 56 / 17), sq_nonneg (2 * sin α + 5 * cos β - 105 / 17),
                sq_nonneg (cos α - 8 / 17), sq_nonneg (sin α - 15 / 17),
                sq_nonneg (cos β - 15 / 17), sq_nonneg (sin β - 8 / 17),
                Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β,
                mul_self_nonneg (cos α - 8 / 17), mul_self_nonneg (sin α - 15 / 17),
                mul_self_nonneg (cos β - 15 / 17), mul_self_nonneg (sin β - 8 / 17),
                Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
    linarith [h_eq, h1]