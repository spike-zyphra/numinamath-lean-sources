import Mathlib

open Real
open scoped BigOperators

theorem number_theory_224868 (a : ℕ → ℕ)
  (h₀ : ∀ n, a n = (∑ i in Finset.Icc 1 n, i^2) % 10) :
  ∃ q : ℚ, q = ∑' n, a n / 10 ^ n := by 
  let q := ∑' n : ℕ, (a n) / 10 ^ n
  use q
  all_goals
    simp