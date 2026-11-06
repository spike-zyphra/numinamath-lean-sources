import Mathlib

theorem number_theory_23354 (n : ℤ) (h : n * (n + 1) * (n + 2) = 720) :
    n + 2 = 10 := by
  have h1 : n * (n + 1) * (n + 2) - 720 = 0 := by
    rw [h]
    ring
  have h2 : (n - 8) * (n^2 + 11 * n + 90) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where n - 8 = 0, so n = 8
    linarith
  · -- Case where n^2 + 11n + 90 = 0
    have : n^2 + 11 * n + 90 = 0 := by
      linarith
    have h5 : n^2 + 11 * n + 90 = 0 := this
    have : n ≤ -90 ∨ n ≥ 1 := by
      by_contra h
      push_neg at h
      have h8 : n * (n + 11) = -90 := by nlinarith
      have h9 : n > -90 := by omega
      have h10 : n < 1 := by omega
      interval_cases n <;> omega
    rcases this with (h1 | h2)
    · -- Case n ≤ -90
      nlinarith [sq_nonneg (n + 55), sq_nonneg (n + 11)]
    · -- Case n ≥ 1
      nlinarith [sq_nonneg (n + 55), sq_nonneg (n + 11)]