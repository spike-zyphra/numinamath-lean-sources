import Mathlib

theorem number_theory_150748 (n : ℤ) (h : 24 ∣ n) :
    ∃ a b c d : ℤ, n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 := by
  rcases h with ⟨k, hk⟩
  use 4 * k + 1, 4 * k - 1, -4 * k, -4 * k
  nlinarith [sq_nonneg (4 * k : ℤ), sq_nonneg ((4 * k + 1 : ℤ) - (4 * k - 1 : ℤ)), sq_nonneg ((4 * k : ℤ) + (4 * k : ℤ)), sq_nonneg ((4 * k + 1 : ℤ) + (4 * k - 1 : ℤ)), sq_nonneg ((-4 * k : ℤ) - (4 * k : ℤ)), sq_nonneg ((4 * k : ℤ) - (-4 * k : ℤ)), sq_nonneg (k : ℤ)]