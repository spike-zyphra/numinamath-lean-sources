import Mathlib

/-890 Let $p$ be the largest prime factor of $10^6-1$.
Show that $p > 25$ and the remainder obtained when $p$ is divided by $25$ is $12$.-/

theorem number_theory_638332
  (p: ℕ) (h: p = sSup (Nat.primeFactors (10^6 - 1))): p > 25 ∧ p % 25 = 12 := by

    -- we show that p = 37 indeed
    suffices p = 37 by simp [this]

    have u: Nat.primeFactors (10^6 - 1) = {3, 7, 11, 13, 37} := by
      native_decide

    rw [u] at h
    clear u
    rw [h]
    clear h
    set s:= ({3, 7, 11, 13, 37}: Finset ℕ)
    have n: s.Nonempty := by
      simp [s]
    rw [Finset.Nonempty.csSup_eq_max' n]
    suffices s.max' n ≤ 37 ∧ 37 ≤ s.max' n by
      omega
    constructor
    .
      rw [Finset.max'_le_iff]
      simp [s]
    .
      have u: 37 ∈ s := by
        simp [s]
      apply Finset.le_max' at u
      tauto
