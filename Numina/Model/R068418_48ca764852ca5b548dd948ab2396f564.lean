import Mathlib

theorem algebra_301977 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, Even n → a n = a (n / 2) + 1)
    (han' : ∀ n ≥ 2, Odd n → a n = 1 / a (n - 1)) :
    ∃ n, a n = 20 / 11 ∧ n = 198 := by 
  use 198
  constructor
  · -- Now we need to compute a 198 through the rules to verify it's 20/11
    norm_num [ha1, han, han', Nat.even_iff, Nat.odd_iff] at *
  all_goals norm_num [ha1, han, han', Nat.even_iff, Nat.odd_iff] at *