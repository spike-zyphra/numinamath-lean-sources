import Mathlib

def a := ∑ i ∈ Finset.range 10, 6 * 10 ^ i
def b := ∑ i ∈ Finset.range 6, 3 * 10 ^ i

theorem number_theory_10152 : Nat.gcd a b = 33 := by
  norm_num [a, b, Finset.sum_range_succ]