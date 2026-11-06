import Mathlib

open Real Set
open scoped Real

theorem algebra_212069 (x : ℝ) (h : cot x = 1 / 2) :
    (cos x - 1 + sin x) * (cos x + 1 - sin x) / (cos x - cos x * sin x) = 4 := by

  have h1 : cos x ≠ 0 := by
    by_contra h2
    have h3 : cot x = 0 := by
      rw [cot_eq_cos_div_sin]
      simp [h2]
    linarith
  have h2 : sin x ≠ 0 := by
    by_contra h3
    have h4 : cot x = 0 := by
      rw [cot_eq_cos_div_sin]
      simp [h3]
    linarith
  have h3 : cos x = (1 / 2) * sin x := by
    have h4 : cos x / sin x = 1 / 2 := by 
      have h5 : cot x = cos x / sin x := by 
        rw [cot_eq_cos_div_sin]
      rw [h5] at h 
      linarith 
    have h5 : cos x = (1 / 2) * sin x := by 
      field_simp [h2] at h4 
      linarith 
    exact h5
  have h4 : cos x ^ 2 + sin x ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq x 
  have h5 : cos x ^ 2 = (1 / 4) * sin x ^ 2 := by 
    rw [h3] 
    ring
  have h6 : sin x ^ 2 = 4 / 5 := by 
    have h7 : cos x ^ 2 + sin x ^ 2 = 1 := by 
      linarith [h4]
    rw [h5] at h7 
    nlinarith 
  have h7 : cos x ^ 2 = 1 / 5 := by 
    nlinarith [h6, h5]
  have h8 : cos x - cos x * sin x ≠ 0 := by 
    by_contra h9
    have h9 : cos x * (1 - sin x) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h9) with h10 h11 
    · -- cos x = 0 
      exfalso 
      apply h1 
      linarith 
    · -- 1 - sin x = 0 
      have h12 : sin x = 1 := by 
        linarith 
      have h13 : sin x ^ 2 = 4 / 5 := by 
        linarith [h6] 
      rw [h12] at h13 
      nlinarith 
  have h9 : (cos x - 1 + sin x) * (cos x + 1 - sin x) = 2 * sin x * (1 - sin x) := by
    nlinarith [h3, Real.sin_sq_add_cos_sq x, h6]
  have h10 : (cos x - cos x * sin x) = cos x * (1 - sin x) := by
    nlinarith 
  rw [h9, h10]
  have h12 : cos x ≠ 0 := h1
  have h13 : 1 - sin x ≠ 0 := by 
    by_contra h14
    have h15 : sin x = 1 := by 
      linarith 
    have h16 : sin x ^ 2 = 4 / 5 := by 
      linarith [h6]
    rw [h15] at h16 
    nlinarith 
  have htan : sin x / cos x = 2 := by 
    field_simp [h1] 
    nlinarith [h3] 
  field_simp [h12, h13]
  <;> nlinarith [htan, Real.sin_sq_add_cos_sq x]