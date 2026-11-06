import Mathlib


theorem number_theory_172664 {p : ℕ} (hp : p.Prime) (h : ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ (q * 10 ^ (Nat.digits 10 r).length + r + 3) = p ^ 2) :
    p = 5 := by
  rcases h with ⟨q, r, hq, hr, heq⟩
  have h1 : r = 2 := by
    by_cases h1 : r > 2
    ·
      have hr1 : r % 2 = 1 := by
        by_contra h2
        push_neg at h2
        have h3 : r % 2 = 0 := by omega
        have h4 : ¬r.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega) (by omega) (by omega)
        tauto
      have h3 : (p ^ 2) % 2 = 0 := by
        have h4 : (r + 3) % 2 = 0 := by
          omega
        have h7 : (q * 10 ^ (Nat.digits 10 r).length) % 2 = 0 := by
          have h8 : (10 ^ (Nat.digits 10 r).length) % 2 = 0 := by
            have h9 : (Nat.digits 10 r).length ≥ 1 := by
              by_contra h9
              push_neg at h9
              have h10 : (Nat.digits 10 r).length = 0 := by omega
              have h11 : r < 10 := by
                by_contra h14
                push_neg at h14
                have h144 : (Nat.digits 10 r).length > 0 := by
                  have h111 : r ≥ 10 := by omega
                  have h155 : (Nat.digits 10 r).length = Nat.log 10 r + 1 := by
                    rw [Nat.digits_len]
                    all_goals linarith
                  have h177 : Nat.log 10 r ≥ 1 := by
                    have h111 : 10 ^ 1 ≤ r := by linarith
                    have h222 : Nat.log 10 r ≥ 1 := by
                      apply Nat.le_log_of_pow_le (by omega) h111
                      all_goals linarith
                    linarith
                  omega
                omega
              interval_cases r <;> norm_num at h10 h1
            have h10 : (10 ^ (Nat.digits 10 r).length) % 2 = 0 := by
              have h11 : (Nat.digits 10 r).length ≥ 1 := h9
              have h12 : 10 % 2 = 0 := by norm_num
              have h13 : ∀ (k : ℕ), k ≥ 1 → (10 ^ k) % 2 = 0 := by
                intro k hk
                induction k with
                | zero =>
                  omega
                | succ k ih =>
                  cases k with
                  | zero =>
                    simp at *
                  | succ k =>
                    simp [Nat.pow_succ, Nat.mul_mod] at *
              apply h13 (Nat.digits 10 r).length h11
            assumption
          simp [Nat.mul_mod, h8] at *
        omega
      have h4 : p % 2 = 0 := by
        by_contra h5
        push_neg at h5
        have h6 : p % 2 = 1 := by
          omega
        have h7 : (p ^ 2) % 2 = 1 := by
          simp [Nat.pow_mod, h6]
        omega
      have hp2 : p = 2 := by
        by_cases hp1 : p > 2
        ·
          have hp3 : p % 2 = 0 := by
            omega
          have hp4 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
          tauto
        ·
          have hp4 : p ≤ 2 := by omega
          interval_cases p <;> try { tauto }
      rw [hp2] at heq
      have h8 : q * 10 ^ (Nat.digits 10 r).length + r + 3 = 4 := by
        nlinarith
      have h9 : q ≥ 2 := by
        by_contra h9
        push_neg at h9
        have h10 : q < 2 := by
          omega
        interval_cases q <;> try { contradiction }
      have h10 : r ≥ 3 := by
        omega
      have h11 : q * 10 ^ (Nat.digits 10 r).length ≥ 2 := by
        have h30 : 10 ^ (Nat.digits 10 r).length ≥ 1 := by
          apply Nat.one_le_pow
          all_goals omega
        nlinarith [show q ≥ 2 from by
          by_contra h9
          push_neg at h9
          have h10 : q < 2 := by
            omega
          interval_cases q <;> try { contradiction }
        ]
      nlinarith
    ·
      have h10 : r ≤ 2 := by omega
      interval_cases r <;> try { tauto }
  have hr2 : r = 2 := h1
  have hr2' : (Nat.digits 10 r).length = 1 := by
    rw [hr2]
    norm_num
  rw [hr2', hr2] at heq
  have heq2 : 10 * q + 5 = p ^ 2 := by
    nlinarith
  have hp2 : p % 5 = 0 := by
    have h1 : p ^ 2 % 5 = 0 := by
      omega
    have : p % 5 = 0 := by
      have h2 : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2)
      ·
        omega
      all_goals
        simp [pow_two, Nat.mul_mod, h2] at h1
    assumption
  have hp3 : p = 5 := by
    by_cases hp1 : p > 5
    ·
      have hp4 : p % 5 = 0 := by
        omega
      have hp5 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega) (by omega) (by omega)
      tauto
    ·
      have hp4 : p ≤ 5 := by
        omega
      interval_cases p <;> try { tauto }
  tauto