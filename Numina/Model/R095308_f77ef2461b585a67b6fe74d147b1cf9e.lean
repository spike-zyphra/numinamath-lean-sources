import Mathlib

open Real

def a : ℕ → ℕ
| n => (∑ i in Finset.Icc 1 n, i^2) % 10

theorem number_theory_132120 : ∃ q : ℚ, q = ∑' n : ℕ, a n / 10 ^ n := by 
  let q := ∑' n : ℕ, (a n) / 10 ^ n
  use q