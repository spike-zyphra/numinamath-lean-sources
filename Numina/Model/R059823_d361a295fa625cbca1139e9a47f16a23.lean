import Mathlib

theorem number_theory_136724 (n : ℕ) :
    (2 * n - 1) ∣ ∑ i in Finset.Icc 1 (2 * n - 1), i := by
  cases n with
  | zero =>
    simp
  | succ n =>
    have h1 : ∑ i in Finset.Icc 1 (2 * (n + 1) - 1), i = (n + 1) * (2 * (n + 1) - 1) := by
      induction n with
      | zero =>
        simp
        <;> try { omega }
      | succ n ih =>
        have h2 : 2 * (n + 1 + 1) - 1 = (2 * (n + 1) - 1) + 2 := by omega
        rw [h2]
        rw [Finset.sum_Icc_succ_top (by omega)]
        rw [Finset.sum_Icc_succ_top (by omega)]
        simp [ih]
        <;> ring_nf <;> omega
    rw [h1]
    use (n + 1)
    <;> ring_nf <;> omega