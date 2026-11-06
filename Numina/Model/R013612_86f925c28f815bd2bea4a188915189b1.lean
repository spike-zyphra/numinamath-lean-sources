import Mathlib

open Real Set
open scoped Real

theorem algebra_12630 {x : ℝ} :
  sin x ^ 4 - cos x ^ 4 = 1 ↔ ∃ k : ℤ, x = k * π + π / 2 := by
  constructor
  · -- Assume $\sin x ^ 4 - \cos x ^ 4 = 1$.
    intro h
    have h1 : sin x ^ 4 - cos x ^ 4 = (sin x ^ 2 - cos x ^ 2) * (sin x ^ 2 + cos x ^ 2) := by
      ring
    rw [h1] at h
    have h2 : sin x ^ 2 + cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    rw [h2] at h
    have h3 : sin x ^ 2 - cos x ^ 2 = 1 := by
      linarith
    have h4 : cos x ^ 2 = 0 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    have h5 : cos x = 0 := by
      nlinarith [h4]
    have h6 : ∃ k : ℤ, x = k * π + π / 2 := by
      have h7 : cos x = 0 := h5
      rw [Real.cos_eq_zero_iff] at h7
      rcases h7 with ⟨k, hk⟩
      refine ⟨k, by linarith [hk]⟩
    exact h6
  · -- Assume $\exists k : ℤ, x = k * π + π / 2$.
    rintro ⟨k, hk⟩
    have h7 : cos x = 0 := by
      rw [hk]
      have : cos (k * π + π / 2) = 0 := by
        have h1 : cos (k * π + π / 2) = cos (k * π) * cos (π / 2) - sin (k * π) * sin (π / 2) := by
          rw [cos_add]
        rw [h1]
        have h2 : cos (π / 2) = 0 := by
          exact cos_pi_div_two
        have h3 : sin (π / 2) = 1 := by
          exact sin_pi_div_two
        have h4 : sin (k * π) = 0 := by
          have : k * π = (k : ℝ) * π := by ring
          rw [this]
          simpa [Real.sin_int_mul_pi] using k
        rw [h2, h3, h4]
        all_goals
          nlinarith
      linarith
    have h8 : sin x ^ 2 = 1 := by
      have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      rw [h7] at h1
      nlinarith
    have h9 : sin x ^ 4 - cos x ^ 4 = 1 := by
      have h8' : sin x ^ 2 = 1 := h8
      have h3 : sin x ^ 4 = 1 := by
        calc
          sin x ^ 4 = (sin x ^ 2) ^ 2 := by ring
          _ = (1) ^ 2 := by rw [h8']
          _ = (1 : ℝ) := by norm_num
      rw [h7]
      nlinarith [h3]
    exact h9