import Mathlib

theorem number_theory_15821 (n : ℕ) (hn : n = ∑ i ∈ Finset.Icc 1 11, (Nat.fib i).factorial) :
    (Nat.digits 10 n)[0]! + (Nat.digits 10 n)[1]! = 5 := by
  rw [hn]
  native_decide