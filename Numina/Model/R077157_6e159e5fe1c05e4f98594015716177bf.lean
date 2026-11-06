import Mathlib

theorem algebra_4424 {n : ℕ} (hn : n = 100) :
    ∑ i in Finset.Icc 1 n, i^2 = n * (n + 1) * (2 * n + 1) / 6 := by
  rw [hn]
  native_decide