import Mathlib

theorem number_theory_181963 (n : ℕ) (h₀ : Even n) (h₁ : ∑ i ∈ Finset.range 10, (n + 2 * i) = 5370) :
    (Nat.primeFactors (n + 2 * 9)) = {2, 3, 7, 13} := by
  simp [Finset.sum_range_succ, Finset.sum_range_zero, add_mul, mul_add] at h₁
  have hn : n = 528 := by linarith
  rw [hn]
  native_decide