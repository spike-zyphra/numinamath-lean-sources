import Mathlib

open Real Set
open scoped Real

theorem algebra_163090 (α : ℝ) :
  (sin (4 * α) ^ 2 + 4 * sin (2 * α) ^ 4 -
    4 * sin (2 * α) ^ 2 * cos (2 * α) ^ 2) /
  (4 - sin (4 * α) ^ 2 - 4 * sin (2 * α) ^ 2) =
  tan (2 * α) ^ 4 := by
  by_cases hcos : cos (2 * α) = 0
  · -- Case $\cos(2\alpha) = 0$
    have hcos2 : cos (2 * α) = 0 := hcos
    have hsin2 : sin (2 * α) ^ 2 = 1 := by
      have hcos2' : cos (2 * α) ^ 2 = 0 := by
        rw [hcos2]
        norm_num
      have h1 : sin (2 * α) ^ 2 + cos (2 * α) ^ 2 = 1 := by
        exact sin_sq_add_cos_sq (2 * α)
      nlinarith [hcos2']
    have h1 : sin (4 * α) = 0 := by
      have h1 : sin (4 * α) = 2 * sin (2 * α) * cos (2 * α) := by
        have h2 : sin (4 * α) = sin (2 * (2 * α)) := by ring
        rw [h2]
        rw [sin_two_mul]
      rw [h1, hcos2]
      norm_num
    have h2 : sin (4 * α) ^ 2 = 0 := by
      rw [h1]
      all_goals norm_num
    have h3' : sin (4 * α) ^ 2 + 4 * sin (2 * α) ^ 4 - 4 * sin (2 * α) ^ 2 * cos (2 * α) ^ 2 = 4 := by
      rw [h2]
      have hsin2' : sin (2 * α) ^ 2 = 1 := hsin2
      have hcos2' : cos (2 * α) ^ 2 = 0 := by
        rw [hcos2]
        norm_num
      nlinarith [hsin2', hcos2']
    have h4' : 4 - sin (4 * α) ^ 2 - 4 * sin (2 * α) ^ 2 = 0 := by
      rw [h2]
      nlinarith [hsin2]
    have h5 : tan (2 * α) = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [hcos2]
    rw [h3', h4', h5]
    norm_num
  · -- Case $\cos(2\alpha) \ne 0$
    have hcos2 : cos (2 * α) ≠ 0 := hcos
    have h1 : sin (4 * α) = 2 * sin (2 * α) * cos (2 * α) := by
      have h2 : sin (4 * α) = sin (2 * (2 * α)) := by ring
      rw [h2]
      rw [sin_two_mul]
    have h2 : sin (4 * α) ^ 2 = 4 * sin (2 * α) ^ 2 * cos (2 * α) ^ 2 := by
      rw [h1]
      ring
    have h3 : sin (4 * α) ^ 2 + 4 * sin (2 * α) ^ 4 - 4 * sin (2 * α) ^ 2 * cos (2 * α) ^ 2 = 4 * sin (2 * α) ^ 4 := by
      rw [h2]
      ring
    have h4 : 4 - sin (4 * α) ^ 2 - 4 * sin (2 * α) ^ 2 = 4 * cos (2 * α) ^ 4 := by
      rw [h2]
      have h5 : cos (2 * α) ^ 2 = 1 - sin (2 * α) ^ 2 := by
        have hcos : cos (2 * α) ^ 2 + sin (2 * α) ^ 2 = 1 := by
          exact cos_sq_add_sin_sq (2 * α)
        linarith
      have h6 : cos (2 * α) ^ 4 = (cos (2 * α) ^ 2) ^ 2 := by ring
      have h7 : cos (2 * α) ^ 4 = (1 - sin (2 * α) ^ 2) ^ 2 := by
        rw [h6]
        rw [h5]
      nlinarith [h7]
    have htan : tan (2 * α) = sin (2 * α) / cos (2 * α) := by
      rw [tan_eq_sin_div_cos]
    have htan2 : tan (2 * α) ^ 4 = (sin (2 * α) / cos (2 * α)) ^ 4 := by
      rw [htan]
    have h5 : (sin (4 * α) ^ 2 + 4 * sin (2 * α) ^ 4 - 4 * sin (2 * α) ^ 2 * cos (2 * α) ^ 2) / (4 - sin (4 * α) ^ 2 - 4 * sin (2 * α) ^ 2) = (4 * sin (2 * α) ^ 4) / (4 * cos (2 * α) ^ 4) := by
      rw [h3, h4]
    rw [h5]
    have h6 : (4 * sin (2 * α) ^ 4) / (4 * cos (2 * α) ^ 4) = (sin (2 * α) / cos (2 * α)) ^ 4 := by
      field_simp [hcos2]
      <;> ring
    rw [h6, htan2]