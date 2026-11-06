import Mathlib

open Real Set

theorem inequalities_106247 (k : ℝ) :
    (∀ x : ℝ, k * x ^ 2 - 4 * k * x + k ^ 2 + 2 * k - 3 > 0) ↔ k > 3 := by
  constructor
  · -- Assume the inequality holds for all x, prove k > 3
    intro h
    by_contra h'
    push_neg at h'
    have h1 := h 0
    have h2 := h 1
    have h3 := h 2
    have h4 := h 3
    have h5 := h 4
    have h6 := h 5
    have h7 := h 2
    have h8 := h (k)
    nlinarith [sq_nonneg (k - 3), sq_nonneg (k), sq_nonneg (k - 1), sq_nonneg (k + 1), sq_nonneg (k - 2), sq_nonneg (k + 3), sq_nonneg (k * (k)), h']
  · -- Assume k > 3, prove the inequality holds for all x
    intro hk x
    nlinarith [sq_nonneg (k * (x - 2) - k), sq_nonneg (x - 2), sq_nonneg (k - 3), sq_nonneg (k), sq_nonneg (k * (x - 2)), mul_pos (show 0 < k by linarith) (show 0 < k - 3 by linarith), mul_pos (show 0 < k by linarith) (show 0 < k by linarith), mul_pos (show 0 < k - 3 by linarith) (show 0 < k - 3 by linarith)]