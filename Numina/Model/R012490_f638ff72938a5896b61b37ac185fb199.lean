import Mathlib

open Real Set
open scoped Real

theorem algebra_188943 {x : ℝ} :
  cos x ^ 3 + cos x ^ 2 - 4 * cos (x / 2) ^ 2 = 0 ↔
  ∃ n : ℤ, x = π * (2 * n + 1) := by
  constructor
  · -- Assume the equation, prove the existence of n
    intro h
    have h1 : cos (x / 2) ^ 2 = (1 + cos x) / 2 := by
      have h2 : cos x = 2 * cos (x / 2) ^ 2 - 1 := by
        rw [←Real.cos_two_mul (x / 2)]
        ring_nf
      linarith
    rw [h1] at h
    have h2 : (cos x + 1) * (cos x ^ 2 - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- $\cos x + 1 = 0$
      have h5 : cos x = -1 := by linarith
      obtain ⟨n, hn⟩ := Real.cos_eq_neg_one_iff.1 h5
      refine ⟨n, by linarith⟩
    · -- $\cos^2 x - 2 = 0$
      have h6 : cos x ^ 2 = 2 := by
        linarith
      have h7 : cos x ^ 2 ≤ 1 := by
        apply cos_sq_le_one
      nlinarith
  · -- Assume the existence of n, prove the equation
    rintro ⟨n, hn⟩
    have h9 : cos x = -1 := by
      have h10 : x = π + 2 * n * π := by
        linarith [hn]
      rw [h10]
      have h11 : cos (π + 2 * n * π) = cos π := by
        have h12 : cos (π + 2 * n * π) = cos π := by
          have h14 : π + 2 * n * π = π + n * (2 * π) := by ring_nf
          rw [h14]
          rw [Real.cos_add_int_mul_two_pi]
        exact h12
      rw [h11]
      rw [Real.cos_pi]
    have h10 : cos (x / 2) = 0 := by
      have h11 : x / 2 = Real.pi / 2 + n * Real.pi := by
        linarith [hn]
      rw [h11]
      have h18 : cos (Real.pi / 2 + n * Real.pi) = 0 := by
        have h20 : cos (Real.pi / 2 + n * Real.pi) = cos (Real.pi / 2) * cos (n * Real.pi) - sin (Real.pi / 2) * sin (n * Real.pi) := by
          rw [cos_add]
        rw [h20]
        have h21 : cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
        have h22 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
        have h23 : sin (n * Real.pi) = 0 := by
          have : sin (n * Real.pi) = 0 := by
            have h24 : n * Real.pi = (n : ℤ) * Real.pi := by ring
            rw [h24]
            simp [Real.sin_int_mul_pi]
          assumption
        rw [h21, h22, h23]
        norm_num
      exact h18
    rw [h9, h10]
    norm_num