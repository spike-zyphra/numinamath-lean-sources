import Mathlib

open Real Set
open scoped Real

theorem algebra_169563 (x : ℝ) :
  2 * (cos (x / 2) ^ 2 * (1 - sin x)) + (cos x) ^ 2 = 0 ↔
  ∃ k : ℤ, x = π / 2 * (4 * k + 1) := by
  constructor
  · -- Assume 2 * (cos (x / 2) ^ 2 * (1 - sin x)) + (cos x) ^ 2 = 0, prove ∃ k : ℤ, x = π / 2 * (4 * k + 1)
    intro h
    have h1 : cos x = 2 * cos (x / 2) ^ 2 - 1 := by
      have h1 : cos x = cos (2 * (x / 2)) := by ring_nf
      rw [h1]
      rw [cos_two_mul]
      <;> ring_nf
    have h2 : cos x ^ 2 = (2 * cos (x / 2) ^ 2 - 1) ^ 2 := by
      rw [h1]
    rw [h2] at h
    have h3 : 4 * (cos (x / 2) ^ 2) ^ 2 - 2 * (cos (x / 2) ^ 2) * (1 + sin x) + 1 = 0 := by
      nlinarith [h]
    have h4 : (1 + sin x) ^ 2 ≥ 4 := by
      nlinarith [sq_nonneg (2 * cos (x / 2) ^ 2 - (1 + sin x) / 2), Real.sin_sq_add_cos_sq x]
    have h5 : sin x ≥ 1 := by
      nlinarith [sq_nonneg (1 + sin x), Real.sin_le_one x]
    have h6 : sin x = 1 := by
      linarith [Real.sin_le_one x, h5]
    have h7 : ∃ k : ℤ, x = π / 2 * (4 * k + 1) := by
      have h8 : sin x = 1 := h6
      obtain ⟨k, hk⟩ := Real.sin_eq_one_iff.1 h8
      use k
      have h11 : x = (Real.pi / 2) + 2 * Real.pi * k := by
        linarith [hk]
      have h12 : x = π / 2 * (4 * k + 1) := by
        rw [show π / 2 * (4 * (k : ℝ) + 1) = π / 2 + 2 * π * (k : ℝ) by ring_nf]
        linarith [h11]
      linarith [h12]
    exact h7
  · -- Assume ∃ k : ℤ, x = π / 2 * (4 * k + 1), prove 2 * (cos (x / 2) ^ 2 * (1 - sin x)) + (cos x) ^ 2 = 0
    rintro ⟨k, hk⟩
    have h1 : x = π / 2 + 2 * π * k := by
      ring_nf at hk ⊢
      linarith
    have h2 : sin x = 1 := by
      rw [show x = π / 2 + 2 * π * k by linarith [h1]]
      have h11 : sin (π / 2 + 2 * π * k) = 1 := by
        have : π / 2 + 2 * π * k = Real.pi / 2 + 2 * Real.pi * k := by ring_nf
        rw [this]
        have h2 : sin (Real.pi / 2 + 2 * Real.pi * (k : ℝ)) = 1 := by
          have h3 : sin (Real.pi / 2 + 2 * Real.pi * (k : ℝ)) = sin (Real.pi / 2) := by
            have h4 : 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) := by ring_nf
            rw [h4]
            rw [sin_add_int_mul_two_pi]
          rw [h3]
          rw [sin_pi_div_two]
        linarith [h2]
      linarith [h11]
    have h3 : cos x = 0 := by
      rw [show x = π / 2 + 2 * π * k by linarith [h1]]
      have h11 : cos (π / 2 + 2 * π * k) = 0 := by
        have : π / 2 + 2 * π * k = Real.pi / 2 + 2 * Real.pi * k := by ring_nf
        rw [this]
        have h2 : cos (Real.pi / 2 + 2 * Real.pi * (k : ℝ)) = 0 := by
          have h3 : cos (Real.pi / 2 + 2 * Real.pi * (k : ℝ)) = cos (Real.pi / 2) := by
            have h4 : 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) := by ring_nf
            rw [h4]
            rw [cos_add_int_mul_two_pi]
          rw [h3]
          rw [cos_pi_div_two]
        linarith [h2]
      linarith [h11]
    rw [h3]
    rw [h2]
    <;> nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq (x / 2)]