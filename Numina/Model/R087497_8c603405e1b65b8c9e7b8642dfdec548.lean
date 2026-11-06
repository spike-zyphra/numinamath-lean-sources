import Mathlib

theorem algebra_317438 (n : ℕ) (hn : n > 15 ∧ n < 30)
    (havg : (n * 66 + 5 * n) / (n + 5 * n) = 75) (havg' : (n * 56 + 5 * n) / (n + 5 * n) = 59) :
    n = 24 := by
  rcases hn with ⟨hn1, hn2⟩
  interval_cases n <;> norm_num at havg havg' ⊢ <;> omega