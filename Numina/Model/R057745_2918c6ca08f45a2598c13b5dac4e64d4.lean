import Mathlib

theorem number_theory_237056 (m n : ℤ) (hm : 0 < m) (hn : 0 < n) :
    83 ∣ 25 * m + 3 * n ↔ 83 ∣ 3 * m + 7 * n := by
  constructor
  · -- Assume 83 divides 25m + 3n, prove 83 divides 3m + 7n
    intro h
    omega
  · -- Assume 83 divides 3m + 7n, prove 83 divides 25m + 3n
    intro h
    omega