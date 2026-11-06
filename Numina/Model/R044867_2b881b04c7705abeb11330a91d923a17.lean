import Mathlib

open Real
theorem algebra_12119 (a b c lambda : ℝ) (h₀ : a^2 + b^2 + c^2 = lambda) (h₁ : lambda > 0) :
    min (min ((a - b)^2) ((b - c)^2)) ((c - a)^2) ≤ lambda / 2 := by

  by_contra h
  push_neg at h

  have h2 : (a - b) ^ 2 > lambda / 2 := by
    by_contra h3
    push_neg at h3
    have h4 : min (min ((a - b) ^ 2) ((b - c) ^ 2)) ((c - a) ^ 2) ≤ (a - b) ^ 2 := by
      simp [min_le_iff]
    nlinarith [h4, h3, h]

  have h3 : (b - c) ^ 2 > lambda / 2 := by
    by_contra h4
    push_neg at h4
    have h5 : min (min ((a - b) ^ 2) ((b - c) ^ 2)) ((c - a) ^ 2) ≤ (b - c) ^ 2 := by
      simp [min_le_iff]
    nlinarith [h5, h4, h]

  have h4 : (c - a) ^ 2 > lambda / 2 := by
    by_contra h5
    push_neg at h5
    have h6 : min (min ((a - b) ^ 2) ((b - c) ^ 2)) ((c - a) ^ 2) ≤ (c - a) ^ 2 := by
      simp [min_le_iff]
    nlinarith [h6, h5, h]

  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    sq_nonneg (a * b + b * c + c * a), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]