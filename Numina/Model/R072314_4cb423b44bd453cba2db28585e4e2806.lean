import Mathlib

open Finset

theorem number_theory_157198 (a : ℕ → ℕ)
    (h₀ : ∀ n, a n = (∑ i ∈ Icc 1 n, i ^ 2) % 10) :
    ∃ q : ℚ, q = ∑' n, a n / 10 ^ n := by 
  let q := ∑' n, (a n) / 10 ^ n
  use q
  all_goals simp