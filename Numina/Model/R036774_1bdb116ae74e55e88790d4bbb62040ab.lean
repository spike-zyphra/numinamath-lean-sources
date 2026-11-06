import Mathlib

theorem number_theory_154549 (n : ℤ) (h : 6 ∣ n) :
    ∃ a b c d : ℤ, n = a^3 + b^3 + c^3 + d^3 := by
  rcases h with ⟨k, hk⟩
  use k + 1, k - 1, -k, -k
  have h_eq : n = 6 * k := by
    linarith
  nlinarith [sq_nonneg (k + 1), sq_nonneg (k - 1), sq_nonneg (-k), sq_nonneg (k + 1 - k), sq_nonneg (-k - k), sq_nonneg (k + 1 - (k - 1)), sq_nonneg (k + 1 - (-k)), sq_nonneg (k - 1 - (-k))]