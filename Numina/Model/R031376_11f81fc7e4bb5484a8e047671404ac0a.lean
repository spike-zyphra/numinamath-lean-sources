import Mathlib

open Real

theorem algebra_179195 {x:ℝ}:
  (cos x)^3 + (cos x)^2 - 4 * (cos (x/2))^2 = 0 ↔
  (∃ k:ℤ, x = (2*k+1) * π) := by
  constructor
  · -- Assume (cos x)^3 + (cos x)^2 - 4 * (cos (x/2))^2 = 0, prove ∃k:ℤ, x = (2*k+1) * π
    intro h
    have h1 : (cos x) ^ 3 + (cos x) ^ 2 - 4 * (cos (x / 2)) ^ 2 = 0 := by linarith
    have h2 : (cos (x / 2)) ^ 2 = (1 + cos x) / 2 := by
      have h4 : cos x = 2 * (cos (x / 2)) ^ 2 - 1 := by
        have h5 : cos x = 2 * (cos (x / 2)) ^ 2 - 1 := by
          rw [← Real.cos_two_mul (x / 2)]
          ring_nf
        linarith
      linarith
    rw [h2] at h1
    have h3 : (cos x + 1) * (cos x ^ 2 - 2) = 0 := by
      nlinarith [sq_nonneg (cos x ^ 2 - 1)]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- cos x + 1 = 0
      have h6 : cos x = -1 := by linarith
      obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.1 h6
      refine ⟨k, ?_⟩
      linarith
    · -- cos x ^ 2 - 2 = 0
      have h6 : cos x ^ 2 = 2 := by linarith
      have h7 : cos x ^ 2 ≤ 1 := by
        apply Real.cos_sq_le_one
      linarith
  · -- Assume ∃k:ℤ, x = (2*k+1) * π, prove (cos x)^3 + (cos x)^2 - 4 * (cos (x/2))^2 = 0
    rintro ⟨k, hk⟩
    have h1 : cos x = -1 := by
      rw [show x = (2 * (k : ℝ) + 1) * Real.pi by
        exact_mod_cast hk
      ]
      have h1 : cos ((2 * (k : ℝ) + 1) * Real.pi) = -1 := by
        have h2 : cos ((2 * (k : ℝ) + 1) * Real.pi) = cos (Real.pi + (k : ℝ) * (2 * Real.pi)) := by
          ring_nf
        rw [h2]
        have h3 : cos (Real.pi + (k : ℝ) * (2 * Real.pi)) = cos Real.pi := by
          have h4 : cos (Real.pi + (k : ℝ) * (2 * Real.pi)) = cos Real.pi := by
            have h5 : Real.pi + (k : ℝ) * (2 * Real.pi) = Real.pi + (k : ℤ) * (2 * Real.pi) := by
              simp at *
            rw [h5]
            rw [Real.cos_add_int_mul_two_pi]
          linarith
        rw [h3]
        norm_num
      linarith
    have h2 : (cos (x / 2)) ^ 2 = 0 := by
      have h3 : (cos (x / 2)) ^ 2 = (1 + cos x) / 2 := by
        have h4 : cos x = 2 * (cos (x / 2)) ^ 2 - 1 := by
          have h5 : cos x = 2 * (cos (x / 2)) ^ 2 - 1 := by
            rw [← Real.cos_two_mul (x / 2)]
            ring_nf
          linarith
        linarith
      rw [h1] at h3
      linarith
    rw [h1, h2]
    norm_num