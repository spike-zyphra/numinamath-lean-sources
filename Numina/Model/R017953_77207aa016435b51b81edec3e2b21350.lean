import Mathlib

theorem number_theory_170898 (m n : ℕ) (hm : m.Prime) (hn : n.Prime)
    (hmn : m < n ∧ n < 5 * m) (hprime : (m + 3 * n).Prime) :
    (m = 2 ∧ n = 3) ∨ (m = 2 ∧ n = 5) ∨ (m = 2 ∧ n = 7) := by
  by_cases h1 : m > 2
  · -- case m > 2
    have h2 : m % 2 = 1 := by
      by_contra h
      push_neg at h
      have h3 : m % 2 = 0 := by
        omega
      have h4 : ¬m.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ m by omega)
        all_goals
          nlinarith
      contradiction
    have h3 : n % 2 = 1 := by
      by_contra h
      push_neg at h
      have h4 : n % 2 = 0 := by
        omega
      have h5 : n > 2 := by
        omega
      have h4 : ¬n.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ n by omega)
        all_goals
          nlinarith
      contradiction
    -- $m + 3n$ is even
    have h4 : (m + 3 * n) % 2 = 0 := by
      omega
    have h5 : m + 3 * n > 2 := by
      have h11 : m > 2 := h1
      have h12 : n > m := hmn.left
      have h13 : n > 2 := by linarith
      omega
    have h6 : ¬ (m + 3 * n).Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (m + 3 * n) by omega)
      all_goals
        nlinarith
    contradiction
  · -- case m ≤ 2
    have h11 : m ≤ 2 := by
      omega
    have h12 : m = 2 := by
      interval_cases m <;> norm_num at hm ⊢
      <;> tauto
    have h11 : m < n := hmn.left
    have h12' : n < 5 * m := hmn.right
    rw [h12] at h11 h12' 
    have h13 : n < 10 := by 
      omega
    have h14 : n = 3 ∨ n = 5 ∨ n = 7 := by
      interval_cases n <;> norm_num at hn hprime ⊢
      <;> try { tauto }
    rcases h14 with (r1 | r2 | r3)
    · -- n = 3
      have h141 : m = 2 := h12
      have h142 : n = 3 := r1
      left
      exact ⟨h141, h142⟩
    · -- n = 5
      have h141 : m = 2 := h12
      have h142 : n = 5 := r2
      right
      left
      exact ⟨h141, h142⟩
    · -- n = 7
      have h141 : m = 2 := h12
      have h142 : n = 7 := r3
      right
      right
      exact ⟨h141, h142⟩