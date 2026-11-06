import Mathlib

open Real

theorem calculus_23085 (x : ℝ) (hx : x = arccos (1 / 3)) : tan x = 2 * sqrt 2 := by 
  rw [hx]
  have h1 : cos (arccos (1 / 3)) = 1 / 3 := by 
    exact cos_arccos (by norm_num) (by norm_num)
  have h2 : sin (arccos (1 / 3)) = 2 * sqrt 2 / 3 := by 
    have hsin : sin (arccos (1 / 3)) ≥ 0 := by 
      apply sin_nonneg_of_nonneg_of_le_pi 
      · -- show $0 \leq \arccos(1/3)$
        apply Real.arccos_nonneg 
      · -- show $\arccos(1/3) \leq \pi$
        apply Real.arccos_le_pi 
    have h3 : sin (arccos (1 / 3)) ^ 2 + cos (arccos (1 / 3)) ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq (arccos (1 / 3))
    rw [h1] at h3 
    have h4 : sin (arccos (1 / 3)) ^ 2 = 8 / 9 := by 
      nlinarith 
    have h5 : sin (arccos (1 / 3)) = 2 * sqrt 2 / 3 := by 
      have h6 : sin (arccos (1 / 3)) ≥ 0 := hsin 
      have h7 : sin (arccos (1 / 3)) = Real.sqrt (8 / 9) := by 
        rw [← h4] 
        field_simp 
      have h8 : Real.sqrt (8 / 9) = 2 * Real.sqrt 2 / 3 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        <;> ring_nf <;> norm_num 
      rw [h7, h8] 
    exact h5 
  have htan : tan (arccos (1 / 3)) = sin (arccos (1 / 3)) / cos (arccos (1 / 3)) := by 
    rw [tan_eq_sin_div_cos] 
  rw [htan, h2, h1] 
  field_simp 
  <;> ring_nf <;> norm_num