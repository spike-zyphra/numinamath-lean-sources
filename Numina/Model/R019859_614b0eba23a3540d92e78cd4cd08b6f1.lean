import Mathlib

open Real

theorem algebra_301030 {f : ℝ → ℝ → ℝ}
    (h₀ : ∀ x y, f x y = if x ≥ y then x ^ 2 * y else x * y ^ 2) (m : ℝ) (h₁ : f 3 m = 36) :
    m = 2 * sqrt 3 := by

  have h2 : f 3 m = if 3 ≥ m then 3 ^ 2 * m else 3 * m ^ 2 := by
    specialize h₀ 3 m
    simpa using h₀
  rw [h2] at h₁
  by_cases h3 : 3 ≥ m
  · -- Case 1: 3 ≥ m
    simp [h3] at h₁
    nlinarith
  · -- Case 2: ¬(3 ≥ m), so 3 < m
    simp [show ¬(3 ≥ m) by linarith] at h₁
    have h4 : m ^ 2 = 12 := by
      nlinarith
    have h5 : m > 0 := by nlinarith
    have h6 : m = Real.sqrt 12 := by
      have h7 : m ^ 2 = 12 := by linarith
      have h8 : m > 0 := by linarith
      have h9 : m = Real.sqrt 12 := by
        rw [← h7]
        field_simp [h8]
      linarith [h9]
    have h7 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h7] at h6
    linarith