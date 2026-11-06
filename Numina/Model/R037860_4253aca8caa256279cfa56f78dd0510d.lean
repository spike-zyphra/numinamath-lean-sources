import Mathlib

set_option maxRecDepth 2000


theorem number_theory_95074 :
IsGreatest {k | ∃ n : ℕ, 3^11 = ∑ i ∈ Finset.range k, (n + i)} 486 := by
  constructor
  · -- Show that 486 is in the set
    use 122
    native_decide
  · -- Show that 486 is greatest
    intro k hk
    rcases hk with ⟨n, hn⟩
    by_contra h
    push_neg at h

    have hk2 : k > 486 := by linarith

    have h3 : 3^11 = ∑ i in Finset.range k, (n + i) := by 
      exact hn

    have h7 : ∑ i in Finset.range k, (n + i) = k * n + k * (k - 1) / 2 := by
      have h8 : ∀ (k : ℕ), ∑ i in Finset.range k, (n + i) = k * n + k * (k - 1) / 2 := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          cases k with
          | zero =>
            simp
          | succ k =>
            simp [Nat.add_assoc, mul_add, Nat.mul_assoc, Nat.add_comm] at *
            <;> ring_nf <;> omega
      apply h8 k

    rw [h7] at h3

    have h8 : k ≤ 729 := by
      by_contra h
      push_neg at h
      have h9 : k > 729 := by linarith
      have h10 : k * n + k * (k - 1) / 2 > (3^11 : ℕ) := by
        have h11 : k ≥ 730 := by omega
        have h12 : k * (k - 1) / 2 ≥ (730 * 729 : ℕ) / 2 := by
          have h14 : k - 1 ≥ 729 := by
            omega
          have h13 : k * (k - 1) ≥ 730 * 729 := by
            nlinarith
          have h15 : k * (k - 1) / 2 ≥ (730 * 729 : ℕ) / 2 := by
            apply Nat.div_le_div
            all_goals
              nlinarith
          linarith
        have h16 : (730 * 729 : ℕ) / 2 > (3^11 : ℕ) := by
          norm_num
        have h17 : k * (k - 1) / 2 > (3^11 : ℕ) := by
          nlinarith
        omega
      omega

    interval_cases k <;> omega