import Mathlib

theorem number_theory_266380 (n : ℕ) (hn : 0 < n) :
    121 ∣ ∑ i ∈ Finset.range (5 * n), 3 ^ i := by 
  have h1 : ∀ (n : ℕ), n > 0 → 121 ∣ ∑ i in Finset.range (5 * n), 3 ^ i := by
    intro n hn 
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        norm_num [Finset.sum_range_succ]
      | succ n =>
        rw [show 5 * (n + 1 + 1) = 5 * (n + 1) + 5 by ring]
        rw [Finset.sum_range_add]
        apply Nat.dvd_add
        · exact ih (by linarith)
        · norm_num [Finset.sum_range_succ]
          <;> ring_nf 
          <;> omega
  specialize h1 n hn 
  simpa using h1