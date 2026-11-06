import Mathlib

theorem number_theory_211699 (n : ℕ) (h : n > 0) :
    ∑ i ∈ Finset.range n, (i + 1)^2 = 42925 ↔ n = 50 := by
  constructor
  · -- First direction: If the sum equals 42925, then n = 50.
    intro h_sum
    have h1 : ∀ (n : ℕ), ∑ i in Finset.range n, (i + 1)^2 = n * (n + 1) * (2 * n + 1) / 6 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [add_assoc]
        ring_nf
        <;> omega
    have eqn : n * (n + 1) * (2 * n + 1) / 6 = 42925 := by
      rw [h1 n] at h_sum
      exact_mod_cast h_sum
    have h2 : n ≤ 50 := by
      by_contra h'
      push_neg at h'
      have h3 : n * (n + 1) * (2 * n + 1) / 6 > 42925 := by
        have h4 : n > 50 := by linarith
        have h5 : n * (n + 1) * (2 * n + 1) ≥ 51 * 52 * 103 := by
          have h6 : n ≥ 51 := by omega
          have h7 : n + 1 ≥ 52 := by omega
          have h8 : 2 * n + 1 ≥ 103 := by omega
          have h9 : (n : ℕ) * (n + 1) * (2 * n + 1) ≥ 51 * 52 * 103 := by
            apply Nat.mul_le_mul
            apply Nat.mul_le_mul
            all_goals linarith
          linarith
        have h6 : n * (n + 1) * (2 * n + 1) / 6 ≥ (51 * 52 * 103) / 6 := by
          omega
        norm_num at h6 ⊢
        linarith
      linarith
    have h3 : n ≥ 50 := by
      by_contra h'
      push_neg at h'
      have h4 : n * (n + 1) * (2 * n + 1) / 6 < 42925 := by
        have h5 : n ≤ 49 := by linarith
        interval_cases n <;> norm_num at *
        <;> omega
      linarith
    linarith
  · -- Second direction: If n = 50, then the sum equals 42925.
    intro h_eq
    rw [h_eq]
    norm_num [Finset.sum_range_succ]