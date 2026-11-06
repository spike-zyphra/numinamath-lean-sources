import Mathlib

open Real

theorem algebra_309103 {S : ℕ → ℝ} (hS : ∀ n, S n = ∑ i in Finset.range n, 8 * (-1 / 3) ^ i) :
    IsLeast {n | |S n - 6| < 1 / 125} 7 := by
  have h1 : |S 7 - 6| < 1 / 125 := by
    rw [hS 7]
    norm_num [abs_of_nonneg, abs_of_nonpos, Finset.sum_range_succ]
    all_goals norm_num [abs_of_nonneg, abs_of_nonpos]
  have h7 : ∀ n : ℕ, |S n - 6| < 1 / 125 → 7 ≤ n := by
    intro n hn
    rw [hS n] at hn
    by_contra h
    push_neg at h
    have h2 : n < 7 := by linarith
    interval_cases n <;> norm_num [abs_of_nonneg, abs_of_nonpos, Finset.sum_range_succ] at hn ⊢
    all_goals norm_num [abs_of_nonneg, abs_of_nonpos] at hn ⊢
  constructor
  · -- Show that 7 is indeed in the set
    exact h1
  · -- Show that 7 is the smallest element in the set
    intro n hn
    have hn' : |S n - 6| < 1 / 125 := by
      simpa using hn
    have h8 : 7 ≤ n := h7 n hn'
    linarith