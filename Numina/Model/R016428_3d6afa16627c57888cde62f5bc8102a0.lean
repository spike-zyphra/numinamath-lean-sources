import Mathlib

open Finset

theorem other_67832 {S : ℕ → ℤ}
    (hS : ∀ n, S n = ∑ i ∈ Icc 1 100, |(n : ℤ) - i|) :
    IsLeast {x | ∃ n, x = S n ∧ 1 < n ∧ n < 100} (S 50) := by
  constructor
  · -- Show that S 50 is indeed in the set
    use 50
    all_goals
      norm_num [hS]
  · -- Show that no value smaller than S 50 is in the set
    intro x hx
    rcases hx with ⟨n, hn, hn1, hn2⟩
    rw [hn] at *
    have h3 : S 50 ≤ S n := by
      rw [hS 50, hS n]
      have h4 : ∑ i in Icc 1 100, |(50 : ℤ) - (i : ℤ)| ≤ ∑ i in Icc 1 100, |(n : ℤ) - (i : ℤ)| := by
        have h5 : n ≥ 2 := by linarith
        have h6 : n ≤ 99 := by linarith
        interval_cases n <;> native_decide
      exact h4
    linarith