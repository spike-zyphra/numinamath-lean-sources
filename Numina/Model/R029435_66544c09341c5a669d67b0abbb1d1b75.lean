import Mathlib

open Real

theorem algebra_267935 (a : ℕ → ℤ) (ha1 : a 1 = 2)
    (han : ∀ n, a (n + 1) = a n ^ 2 - a n + 1) :
    1 - 1 / 2018 ^ 2018 < ∑ n in Finset.Icc 1 2018, 1 / a n ∧
    ∑ n in Finset.Icc 1 2018, 1 / a n < 1 := by
  have h1 := han 0
  rw [ha1] at h1
  norm_num at h1
  all_goals
    have h2 : a 0 ^ 2 - a 0 - 1 = 0 := by nlinarith
    have h3 : a 0 ≤ 1 := by nlinarith [sq_nonneg (a 0 - 1)]
    have h4 : a 0 ≥ -1 := by nlinarith [sq_nonneg (a 0 - 1)]
    have h5 : a 0 = 0 ∨ a 0 = 1 ∨ a 0 = -1 := by
      interval_cases a 0 <;> omega
    rcases h5 with (h5 | h5 | h5)
    · -- a 0 = 0 leads to a contradiction
      rw [show a 0 = (0 : ℤ) by linarith] at h2
      norm_num at h2
    · -- a 0 = 1 leads to a contradiction
      rw [show a 0 = (1 : ℤ) by linarith] at h2
      norm_num at h2
    · -- a 0 = -1 leads to a contradiction
      rw [show a 0 = (-1 : ℤ) by linarith] at h2
      norm_num at h2