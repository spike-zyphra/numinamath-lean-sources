import Mathlib

def a (n : ℕ) := (∑ i in Finset.Icc 1 n, i^2) % 10

theorem number_theory_74617 : ∃ q : ℚ, q = ∑' n, a n / 10 ^ n := by
  let q := ∑' n, (a n) / 10 ^ n
  use q