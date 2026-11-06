import Mathlib

theorem algebra_109876 {n : ℕ} (hn : n > 0) :
    ∑ k in Finset.Icc 1 n, k^2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => linarith
  | succ n ih =>
    cases n
    · simp
    · simp [Finset.sum_Icc_succ_top, ih]
      ring_nf
      <;> omega