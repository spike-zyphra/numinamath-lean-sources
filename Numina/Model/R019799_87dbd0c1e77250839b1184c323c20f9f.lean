import Mathlib

theorem algebra_197121 (x : ℝ) (h : 8.469 * (Real.sin x)^4 + 2 * (Real.cos x)^3 + 2 * (Real.sin x)^2 - Real.cos x + 1 = 0) :
    ∃ k : ℤ, x = Real.pi * (2 * k + 1) := by
  have h1 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    linarith
  have h2 : Real.sin x ^ 4 = (1 - Real.cos x ^ 2) ^ 2 := by
    calc
      Real.sin x ^ 4 = (Real.sin x ^ 2) ^ 2 := by ring
      _ = (1 - Real.cos x ^ 2) ^ 2 := by rw [h1]
  rw [h2] at h
  have h3 : 8.469 * (1 - Real.cos x ^ 2) ^ 2 + 2 * (Real.cos x) ^ 3 + 2 * (1 - Real.cos x ^ 2) - (Real.cos x) + 1 = 0 := by
    nlinarith
  have h4 : Real.cos x = -1 := by
    nlinarith [sq_nonneg (Real.cos x + 1), sq_nonneg ((1 - Real.cos x ^ 2) ), sq_nonneg (Real.sin x ^ 2), sq_nonneg ((Real.cos x) ^ 2 - 1), sq_nonneg ((1 - Real.cos x ^ 2) ^ 2), sq_nonneg ((Real.cos x ^ 2) ), sq_nonneg ((1 - Real.cos x ^ 2) ), sq_nonneg ((Real.sin x) ^ 2) ]
  have h6 : Real.cos x = -1 := by linarith
  obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.1 h6
  refine ⟨k, by linarith [hk]⟩