import Mathlib

theorem algebra_106874 (n : ℕ) :
    ∑ k in Finset.Icc 0 n, k^2 = n * (n + 1) * (2 * n + 1) / 6 := by
  have h1 : ∀ (n : ℕ), ∑ k in Finset.Icc 0 n, k ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      ring_nf
      omega
  specialize h1 n
  simpa using h1