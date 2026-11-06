import Mathlib

open Real Set
open scoped Real

theorem algebra_6244 : IsGreatest {y : ℝ | ∃ x, y = 2 * (cos x)^2 + sin x + 1} (3 + 1/8) := by
  constructor
  · -- Show 3 + 1/8 is achievable, when sin x = 1/4
    use arcsin (1 / 4)
    have h1 : cos (arcsin (1 / 4)) ^ 2 = 1 - (1 / 4) ^ 2 := by 
      rw [cos_sq']
      rw [sin_arcsin]
      all_goals norm_num
    have h2 : sin (arcsin (1 / 4)) = 1 / 4 := by 
      apply sin_arcsin
      all_goals norm_num
    rw [h1, h2]
    norm_num
  · -- Show 3 + 1/8 is the greatest
    intro y
    rintro ⟨x, hx⟩
    have h : 2 * (cos x) ^ 2 + sin x + 1 = 3 - 2 * (sin x) ^ 2 + sin x := by 
      have h1 : (cos x) ^ 2 = 1 - (sin x) ^ 2 := by 
        rw [←Real.cos_sq_add_sin_sq x]
        linarith
      rw [h1]
      ring
    rw [h] at hx
    have h2 : (4 * sin x - 1) ^ 2 ≥ 0 := by 
      apply sq_nonneg
    nlinarith [Real.sin_sq_le_one x, h2]