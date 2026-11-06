import Mathlib

open Finset

def a : ℕ → ℕ
| n => (∑ i ∈ Icc 1 n, i^2) % 10

theorem number_theory_324959 : ∃ q : ℚ, q = ∑' n, a n / 10 ^ n := by 
  let q := ∑' n : ℕ, (a n) / 10 ^ n
  use q
  all_goals simp