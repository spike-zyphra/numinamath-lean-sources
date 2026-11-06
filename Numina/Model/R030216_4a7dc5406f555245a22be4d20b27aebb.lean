import Mathlib

theorem algebra_188028 : IsGreatest (Set.range (8 * Real.sin + 15 * Real.cos : ℝ → ℝ)) 17 := by
  constructor
  · -- Show 17 is in the range
    use (Real.arcsin (8 / 17))
    have h1 : Real.sin (Real.arcsin (8 / 17 : ℝ)) = (8 / 17 : ℝ) := by
      apply Real.sin_arcsin
      · norm_num
      · norm_num
    have h2 : Real.cos (Real.arcsin (8 / 17 : ℝ)) = (15 / 17 : ℝ) := by
      have hcos : Real.cos (Real.arcsin (8 / 17 : ℝ)) = Real.sqrt (1 - (8 / 17 : ℝ) ^ 2) := by
        rw [Real.cos_arcsin]
      rw [hcos]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
    simp [h1, h2]
    norm_num
  · -- Show that no value greater than 17 is in the range
    intro y
    rintro ⟨x, hx⟩
    have h_eq : (8 * Real.sin x + 15 * Real.cos x) = y := by
      simpa using hx
    have h_le : 8 * Real.sin x + 15 * Real.cos x ≤ 17 := by
      have h1 : (8 * Real.sin x + 15 * Real.cos x) ^ 2 ≤ 289 := by
        have h1 : (8 * Real.sin x + 15 * Real.cos x) ^ 2 ≤ (8 ^ 2 + 15 ^ 2) * (Real.sin x ^ 2 + Real.cos x ^ 2) := by
          nlinarith [sq_nonneg (8 * Real.cos x - 15 * Real.sin x), sq_nonneg (8 * Real.sin x + 15 * Real.cos x), sq_nonneg (Real.sin x ^ 2 + Real.cos x ^ 2 - 1)]
        have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        rw [h2] at h1
        nlinarith
      nlinarith [sq_nonneg (8 * Real.sin x + 15 * Real.cos x - 17), Real.sin_sq_add_cos_sq x]
    linarith [h_eq, h_le]