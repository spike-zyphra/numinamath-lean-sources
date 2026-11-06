import Mathlib

theorem algebra_115407 {S : ℕ → ℤ}
    (hS : ∀ n, S n = ∑ i in Finset.Icc 1 n, i ^ 2) :
    ∀ n, S n = n * (n + 1) * (2 * n + 1) / 6 := by
  intro n
  induction n with
  | zero =>
    simp [hS]
  | succ n ih =>
    have h1 : S (n + 1) = S n + (n + 1 : ℕ) ^ 2 := by
      rw [hS (n + 1), hS n]
      simp [Finset.sum_Icc_succ_top, pow_two]
      <;> ring
    rw [h1]
    rw [ih]
    simp [pow_two]
    ring_nf
    <;> omega