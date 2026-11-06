import Mathlib
open Nat

/- Determine all prime numbers $p$ and $q$ such that $p^{q}+1$ is also prime.-/
theorem number_theory_600011 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
  (p ^ q + 1).Prime ↔ p = 2 ∧ q = 2 := by
  constructor
  · -- Forward: If $p^q + 1$ is prime, then $p = 2$ and $q = 2$.
    intro h_prime
    have h_p_eq_2 : p = 2 := by
      have : p ≥ 2 := hp.two_le
      have : p = 2 ∨ p ≥ 3 := by
        cases Nat.eq_or_lt_of_le this with
        | inl h_eq => left; exact h_eq.symm
        | inr h_lt => right; linarith
      cases this with
      | inl h_eq => exact h_eq
      | inr h_ge_3 =>
        -- If $p ≥ 3$, $p$ is odd, so $p^q + 1$ is even and composite.
        have : p ^ q ≡ 1 [MOD 2] := by
          have h_p_ge_3 : p ≥ 3 := h_ge_3
          have h_p_mod : p ≡ 1 [MOD 2] := by
            have h_p_ne_2 : p ≠ 2 := by linarith [h_p_ge_3]
            have h_fact : Fact (Nat.Prime p) := ⟨hp⟩
            have : p % 2 = 1 := Nat.Prime.mod_two_eq_one_iff_ne_two.mpr h_p_ne_2
            tauto
          have : 1 ^ q = 1 := by norm_num
          rw [← this]
          apply Nat.ModEq.pow q h_p_mod
        have h_sum_mod: p ^ q + 1 ≡ 1 + 1 [MOD 2] := by
          apply Nat.ModEq.add this
          tauto
        -- Show $p^q + 1 ≡ 0 (mod 2)$, implying it is even.
        have h_eq_zero_mod: p ^ q + 1 ≡ 0 [MOD 2] := by tauto
        have h_dvd_2: 2 ∣ p ^ q + 1 := by
          apply Nat.dvd_of_mod_eq_zero
          have : (p ^ q + 1) % 2 = 0 := by
            apply Nat.mod_eq_of_modEq h_eq_zero_mod
            norm_num
          exact this
        have h_pq_ge_3 : p ^ q + 1 ≥ 3 := by
          have : p ≥ 3 := h_ge_3
          have : q ≥ 2 := hq.two_le
          have : p ^ q ≥ p ^ 2 := by
            apply Nat.pow_le_pow_of_le_right
            exact (by linarith [h_ge_3])
            linarith
          have : p ^ 2 ≥ 3 ^ 2 := by
            apply Nat.pow_le_pow_of_le_left
            exact h_ge_3
          have : p ^ q ≥ 3 ^ 2 := by omega
          nlinarith
        -- Ensure $p^q + 1 ≠ 2$, so it is composite if divisible by $2$.
        have h_pq_ne_2 : p ^ q + 1 ≠ 2 := by
          linarith
        -- Conclude $p^q + 1$ is not prime, contradicting h_prime.
        have : ¬Nat.Prime (p ^ q + 1) := by
          have h_pq_ge_2 : 2 ≤ p ^ q + 1 := by
            linarith [h_pq_ge_3]
          apply (Nat.not_prime_iff_exists_dvd_ne h_pq_ge_2).mpr
          use 2
          constructor
          · exact h_dvd_2
          · constructor
            · norm_num
            · exact h_pq_ne_2.symm
        contradiction
    -- Prove $q = 2$ by showing that $q ≥ 3$ leads to a contradiction.
    have h_q_eq_2 : q = 2 := by
      have h_q_ge_2 : q ≥ 2 := hq.two_le
      have h_q_cases : q = 2 ∨ q ≥ 3 := by
        cases Nat.eq_or_lt_of_le h_q_ge_2 with
        | inl h_eq => left; exact h_eq.symm
        | inr h_lt => right; linarith
      cases h_q_cases with
      | inl h_eq => exact h_eq
      | inr h_q_ge_3 =>
        -- If $q ≥ 3$, $q$ is odd, so $2^q + 1$ is divisible by $3$.
        have h_dvd_3 : 3 ∣ 2 ^ q + 1 := by
          have : q ≥ 3 := h_q_ge_3
          have h_q_ne_2 : q ≠ 2 := by linarith
          have h_fact : Fact (Nat.Prime q) := ⟨hq⟩
          have h_q_odd: q % 2 = 1 := Nat.Prime.mod_two_eq_one_iff_ne_two.mpr h_q_ne_2
          -- Prove $2^q + 1 ≡ 0 (mod 3)$.
          have h_mod3_eq_zero: 2 ^ q + 1 ≡ 0 [MOD 3] := by
            have h_2_mod_3 : 2 ≡ 2 [MOD 3] := by tauto
            have h_2q_mod_3 : 2 ^ q ≡ 2 [MOD 3] := by
              have : q = 2 * (q / 2) + 1 := by
                have h₁: 2 * (q / 2) + q % 2 = q := by rw [div_add_mod]
                omega
              rw [this]
              have : 2 ^ (2 * (q / 2) + 1) = 2 ^ (2 * (q / 2)) * 2 := by
                rw [pow_add, pow_one]
              rw [this]
              have : 2 ^ (2 * (q / 2)) ≡ 1 [MOD 3] := by
                have h₁: 2 ^ 2 ≡ 1 [MOD 3] := by tauto
                have h₂: 2 ^ (2 * (q / 2)) = (2 ^ 2) ^ (q / 2) := by rw [Nat.pow_mul]
                have : 1 ^ (q / 2) = 1 := by norm_num
                rw [h₂, ← this]
                apply Nat.ModEq.pow (q / 2) h₁
              have : 2 ^ (2 * (q / 2)) * 2 ≡ 1 * 2 [MOD 3] := by
                apply Nat.ModEq.mul this h_2_mod_3
              tauto
            have : 2 ^ q + 1 ≡ 2 + 1 [MOD 3] := by
              apply Nat.ModEq.add h_2q_mod_3
              tauto
            tauto
          apply Nat.dvd_of_mod_eq_zero h_mod3_eq_zero
        -- Show $2^q + 1 ≥ 9$ to ensure it is not the prime $3$.
        have h_pq_ge_9 : 2 ^ q + 1 ≥ 9 := by
          have h_q_ge_3 : q ≥ 3 := h_q_ge_3
          have : 2 ^ q ≥ 2 ^ 3 := by
            apply Nat.pow_le_pow_of_le_right
            · norm_num
            · exact h_q_ge_3
          have : 2 ^ q ≥ 8 := by
            apply Nat.le_trans this
            norm_num
          linarith
        have h_pq_ne_3 : 2 ^ q + 1 ≠ 3 := by
          linarith [h_pq_ge_9]
        have h_not_prime : ¬Nat.Prime (2 ^ q + 1) := by
          have h_pq_ge_2 : 2 ≤ 2 ^ q + 1 := by nlinarith
          apply (Nat.not_prime_iff_exists_dvd_ne h_pq_ge_2).mpr
          use 3
          constructor
          · exact h_dvd_3
          · constructor
            · norm_num
            · exact h_pq_ne_3.symm
        rw [← h_p_eq_2] at h_not_prime
        contradiction
    -- Combine results to conclude $p = 2$ and $q = 2$.
    exact And.intro h_p_eq_2 h_q_eq_2
  · -- Backward: If $p = 2$ and $q = 2$, then $p^q + 1$ is prime.
    intro h
    cases h with | intro hp hq =>
      rw [hp, hq]
      norm_num
