import Mathlib
open Nat 

/-Let $p, q$, and $r$ be distinct primes. Prove that $p+q+r+p q r$ is composite.-/
theorem number_theory_600026
  (p q r : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
  (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : ¬ Nat.Prime (p + q + r + p * q * r) := by
  -- Prove that $n = p + q + r + p * q * r > 2$.
  have h_n_gt_2 : p + q + r + p * q * r > 2 := by
    have h_p_ge_2 : p ≥ 2 := Nat.Prime.two_le hp
    have h_q_ge_2 : q ≥ 2 := Nat.Prime.two_le hq
    have h_r_ge_2 : r ≥ 2 := Nat.Prime.two_le hr
    have h_pq_ge_4 : p * q ≥ 4 := by nlinarith
    have h_pqr_ge_8 : p * q * r ≥ 8 := by nlinarith
    nlinarith
  -- Prove that n is divisible by $2$ using proof by contradiction.
  have h_n_div_2 : 2 ∣ p + q + r + p * q * r := by
    by_contra h_not_div_2
    have h_p_mod_2 : p % 2 = 0 ∨ p % 2 = 1 := by omega
    have h_q_mod_2 : q % 2 = 0 ∨ q % 2 = 1 := by omega
    have h_r_mod_2 : r % 2 = 0 ∨ r % 2 = 1 := by omega
    have h_p_odd : p % 2 = 1 := by
      by_contra h
      have h_p_mod_0 : p % 2 = 0 := by omega
      have h_p_div_2 : 2 ∣ p := by
        omega
      have h_p_eq_2 : p = 2 := by
        have h_p_prime := Nat.Prime.eq_two_or_odd hp
        omega
      have h_q_odd : q % 2 = 1 := by
        by_contra h'
        have h_q_mod_0 : q % 2 = 0 := by omega
        have h_q_div_2 : 2 ∣ q := by
          omega
        have h_q_eq_2 : q = 2 := by
          have h_q_prime := Nat.Prime.eq_two_or_odd hq
          omega
        have h_p_eq_q : p = q := by
          omega
        contradiction
      have h_r_odd : r % 2 = 1 := by
        by_contra h'
        have h_r_mod_0 : r % 2 = 0 := by omega
        have h_r_div_2 : 2 ∣ r := by
          omega
        have h_r_eq_2 : r = 2 := by
          have h_r_prime := Nat.Prime.eq_two_or_odd hr
          omega
        have h_p_eq_r : p = r := by
          omega
        contradiction
      -- Case $1$: $p = 2$, $q$ and $r$ odd, show $n$ is even.
      have h_n_even : (p + q + r + p * q * r) % 2 = 0 := by
        have h_sum_mod_0 : (p + q + r) % 2 = 0 := by omega
        have h_pqr_mod_0 : (p * q * r) % 2 = 0 := by
          rw [h_p_eq_2]
          simp [Nat.mul_mod]
        omega
      have h_n_div_2' : 2 ∣ (p + q + r + p * q * r) := by omega
      contradiction
    have h_q_odd : q % 2 = 1 := by
      by_contra h
      have h_q_mod_0 : q % 2 = 0 := by omega
      have h_q_div_2 : 2 ∣ q := by
        omega
      have h_q_eq_2 : q = 2 := by
        have h_q_prime := Nat.Prime.eq_two_or_odd hq
        omega
      have h_p_odd : p % 2 = 1 := by
        by_contra h'
        have h_p_mod_0 : p % 2 = 0 := by omega
        have h_p_div_2 : 2 ∣ p := by
          omega
        have h_p_eq_2 : p = 2 := by
          have h_p_prime := Nat.Prime.eq_two_or_odd hp
          omega
        have h_p_eq_q : p = q := by
          omega
        contradiction
      have h_r_odd : r % 2 = 1 := by
        by_contra h'
        have h_r_mod_0 : r % 2 = 0 := by omega
        have h_r_div_2 : 2 ∣ r := by
          omega
        have h_r_eq_2 : r = 2 := by
          have h_r_prime := Nat.Prime.eq_two_or_odd hr
          omega
        have h_q_eq_r : q = r := by
          omega
        contradiction
      -- Case $2$: $q = 2$, $p$ and $r$ odd, show $n$ is even.
      have h_n_even : (p + q + r + p * q * r) % 2 = 0 := by
        have h_sum_mod_0 : (p + q + r) % 2 = 0 := by omega
        have h_pqr_mod_0 : (p * q * r) % 2 = 0 := by
          rw [h_q_eq_2]
          simp [Nat.mul_mod]
        omega
      have h_n_div_2' : 2 ∣ (p + q + r + p * q * r) := by omega
      contradiction
    have h_r_odd : r % 2 = 1 := by
      by_contra h
      have h_r_mod_0 : r % 2 = 0 := by omega
      have h_r_div_2 : 2 ∣ r := by
        omega
      have h_r_eq_2 : r = 2 := by
        have h_r_prime := Nat.Prime.eq_two_or_odd hr
        omega
      have h_p_odd : p % 2 = 1 := by
        by_contra h'
        have h_p_mod_0 : p % 2 = 0 := by omega
        have h_p_div_2 : 2 ∣ p := by
          omega
        have h_p_eq_2 : p = 2 := by
          have h_p_prime := Nat.Prime.eq_two_or_odd hp
          omega
        have h_p_eq_r : p = r := by
          omega
        contradiction
      have h_q_odd : q % 2 = 1 := by
        by_contra h'
        have h_q_mod_0 : q % 2 = 0 := by omega
        have h_q_div_2 : 2 ∣ q := by
          omega
        have h_q_eq_2 : q = 2 := by
          have h_q_prime := Nat.Prime.eq_two_or_odd hq
          omega
        have h_q_eq_r : q = r := by
          omega
        contradiction
      -- Case $3$: $r = 2$, $p$ and $q$ odd, show $n$ is even.
      have h_n_even : (p + q + r + p * q * r) % 2 = 0 := by
        have h_sum_mod_0 : (p + q + r) % 2 = 0 := by omega
        have h_pqr_mod_0 : (p * q * r) % 2 = 0 := by
          rw [h_r_eq_2]
          simp [Nat.mul_mod]
        omega
      have h_n_div_2' : 2 ∣ (p + q + r + p * q * r) := by omega
      contradiction
    -- Case $4$: $p, q, r$ all odd, show $n$ is even.
    have h_n_even : (p + q + r + p * q * r) % 2 = 0 := by
      have h_p_odd : p % 2 = 1 := h_p_odd
      have h_q_odd : q % 2 = 1 := h_q_odd
      have h_r_odd : r % 2 = 1 := h_r_odd
      have h_n_mod_0 : (p + q + r + p * q * r) % 2 = 0 := by
        simp [h_p_odd, h_q_odd, h_r_odd, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
      exact h_n_mod_0
    omega
  -- Conclude $n$ is not prime since it is divisible by $2$ and greater than $2$.
  have h_n_not_prime : ¬ Nat.Prime (p + q + r + p * q * r) := by
    intro h_n_prime
    have h_prime_dvd := Nat.Prime.eq_one_or_self_of_dvd h_n_prime 2
    have h_n_div_2' : 2 ∣ p + q + r + p * q * r := h_n_div_2
    have h_n_gt_2' : p + q + r + p * q * r > 2 := h_n_gt_2
    have h_n_eq_2 : p + q + r + p * q * r = 2 := by
      omega
    have h_n_gt_2'' : p + q + r + p * q * r > 2 := h_n_gt_2
    linarith
  exact h_n_not_prime
