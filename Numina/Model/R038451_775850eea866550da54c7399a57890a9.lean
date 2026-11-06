import Mathlib

theorem inequalities_66609 (x : ℝ) : x^2 * Real.sin x + x * Real.cos x + x^2 + 1 / 2 > 0 := by
  have h1 : -1 ≤ Real.sin x ∧ Real.sin x ≤ 1 := Real.sin_mem_Icc x
  have h2 : -1 ≤ Real.cos x ∧ Real.cos x ≤ 1 := Real.cos_mem_Icc x
  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h4 : Real.sin x + 1 ≥ 0 := by linarith
  by_cases h : Real.sin x > -1
  · -- If Real.sin x > -1, then Real.sin x + 1 > 0.
    have h6 : Real.sin x + 1 > 0 := by linarith
    have h7 : x^2 * Real.sin x + x * Real.cos x + x^2 + 1 / 2 =
        (Real.sin x + 1) * (x + Real.cos x / (2 * (Real.sin x + 1))) ^ 2 + (1 / 2 - Real.cos x ^ 2 / (4 * (Real.sin x + 1))) := by
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [h7]
    have h9 : 1 / 2 - Real.cos x ^ 2 / (4 * (Real.sin x + 1)) > 0 := by
      have h10 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      have h11 : 2 * (Real.sin x + 1) ≥ Real.cos x ^ 2 := by
        nlinarith [sq_nonneg (Real.sin x + 1), Real.sin_le_one x, Real.neg_one_le_sin x]
      have h12 : Real.cos x ^ 2 / (4 * (Real.sin x + 1)) < 1 / 2 := by
        apply (div_lt_iff₀ (by linarith)).mpr
        nlinarith
      linarith
    have h13 : (Real.sin x + 1) * (x + Real.cos x / (2 * (Real.sin x + 1))) ^ 2 ≥ 0 := by
      positivity
    linarith [h13, h9]
  · -- Case Real.sin x ≤ -1
    have h14 : Real.sin x = -1 := by linarith [h1.1, h1.2, h]
    have h15 : Real.cos x = 0 := by
      have h16 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      rw [h14] at h16
      nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]
    rw [h14, h15]
    nlinarith