import Mathlib
open Nat

/- 13. Let $n \in \mathbf{N}^{*}, n>1, p$ be a prime number. Given
$$n|(p-1), p|\left(n^{3}-1\right)$$

Prove: $4 p-3$ is a perfect square. -/
theorem number_theory_7622 (n p : ℕ) (hp : Nat.Prime p) (hn : 1 < n)
    (hnp : n ∣ (p - 1)) (hpn : p ∣ (n ^ 3 - 1)) :
    IsSquare (4 * p - 3) := by
  -- Prove that $4p - 3$ is a perfect square, i.e., there exists k such that $4p - 3 = k^2$.
  -- From $n ∣ (p - 1)$, deduce $n < p$.
  have h_n_lt_p : n < p := by
    have h_n_divides_p_minus_one : n ∣ p - 1 := hnp
    have h_p_minus_one_ge_n : p - 1 ≥ n := Nat.le_of_dvd (by
      have h_p_ge_two : p ≥ 2 := Nat.Prime.two_le hp
      omega) h_n_divides_p_minus_one
    have h_p_gt_n : p > n := by omega
    omega
  -- From $p ∣ (n^3 - 1)$, deduce $p ∣ (n - 1)(n^2 + n + 1)$.
  have h_p_divides_factors : p ∣ (n - 1) * (n ^ 2 + n + 1) := by
    have h_cube_minus_one_identity : n ^ 3 - 1 = (n - 1) * (n ^ 2 + n + 1) := by
      cases n with
      | zero => contradiction
      | succ n =>
        cases n with
        | zero => contradiction
        | succ n =>
          simp
          ring_nf at *
          omega
    rwa [h_cube_minus_one_identity] at hpn
  -- Since $p$ is prime, $p$ divides either $n - 1$ or $n^2 + n + 1$.
  have h_p_divides_either : p ∣ (n - 1) ∨ p ∣ (n ^ 2 + n + 1) := by
    exact (Nat.Prime.dvd_mul hp).mp h_p_divides_factors
  -- From $n ∣ (p - 1)$, deduce $p = n * m + 1$ for some $m > 0$.
  have h_p_form_nm_plus_one : ∃ m, m > 0 ∧ p = n * m + 1 := by
    have h_n_divides_p_minus_one : n ∣ p - 1 := hnp
    have h_exists_m : ∃ m : ℕ, p - 1 = n * m := by
      obtain ⟨c, hc⟩ := exists_eq_mul_left_of_dvd h_n_divides_p_minus_one
      exists c
      rw [mul_comm] at hc
      exact hc
    obtain ⟨m, h_p_minus_one_eq_nm⟩ := h_exists_m
    have h_p_eq_nm_plus_one : p = n * m + 1 := by omega
    have h_m_positive : m > 0 := by
      by_contra h
      have h_m_zero : m = 0 := by omega
      rw [h_m_zero] at h_p_eq_nm_plus_one
      have h_p_eq_one : p = 1 := by omega
      have h_p_ge_two : p ≥ 2 := Nat.Prime.two_le hp
      omega
    exact ⟨m, h_m_positive, by omega⟩
  obtain ⟨m, h_m_positive, h_p_eq_nm_plus_one⟩ := h_p_form_nm_plus_one
  -- Prove $m = n + 1$.
  have h_m_eq_n_plus_one : m = n + 1 := by
    -- Prove $p$ divides $n^2 + n + 1$ by eliminating $p ∣ n - 1$.
    have h_p_divides_n2n1 : p ∣ n ^ 2 + n + 1 := by
      cases h_p_divides_either with
      | inl h_p_div_n_minus_one =>
        have h_n_minus_one_lt_p : n - 1 < p := by omega
        have h_n_minus_one_ge_p : n - 1 ≥ p := Nat.le_of_dvd (by omega) h_p_div_n_minus_one
        linarith
      | inr h_p_n2n1 => exact h_p_n2n1
    -- Rewrite $n^2 + n + 1$ to include $n * (n + 1 - m) + p$.
    have h_n2n1_eq_nm_term_plus_p : n ^ 2 + n + 1 = n * (n + 1 - m) + p := by
      calc n ^ 2 + n + 1
        _ = n ^ 2 + n + (n * m + 1) - n * m := by omega
        _ = n ^ 2 + n + p - n * m := by rw [← h_p_eq_nm_plus_one]
        _ = n ^ 2 + n - n * m + p := by
          have h₁: n ^ 2 + n + p - n * m = p + n ^ 2 + n - n * m := by
            rw [add_comm (n ^ 2 + n) p]
            ring_nf
          have h₂: n ^ 2 + n - n * m + p = p + n ^ 2 + n - n * m := by
            have h_nm_le : n * m ≤ n ^ 2 + n := by
              have h_p_le : p ≤ n ^ 2 + n + 1 := Nat.le_of_dvd (by nlinarith) h_p_divides_n2n1
              linarith
            rw [add_comm (n ^ 2 + n - n * m) p, ← Nat.add_sub_assoc h_nm_le p]
            ring_nf
          rw [h₁, h₂]
        _ = n * (n + 1 - m) + p := by
          have h₁ : n ^ 2 + n = n * (n + 1) := by ring
          have h₂ : n * (n + 1) - n * m = n * (n + 1 - m) := by
            rw [mul_comm, mul_comm n m, ← Nat.mul_sub_right_distrib, mul_comm]
          rw [h₁, h₂]
    -- Deduce $p ∣ n * (n + 1 - m)$.
    have h_p_divides_nm_term : p ∣ n * (n + 1 - m) := by
      rw [h_n2n1_eq_nm_term_plus_p] at h_p_divides_n2n1
      have h_sub_p : n * (n + 1 - m) + p - p = n * (n + 1 - m) := by omega
      rw [← h_sub_p]
      exact Nat.dvd_sub' h_p_divides_n2n1 (Nat.dvd_refl p)
    -- Bound $n + 1 - m$ to be between $0$ and $n$.
    have h_nm_bound_upper : n + 1 - m ≤ n := by omega
    have h_nm_bound_lower : n + 1 - m ≥ 0 := by omega
    -- Prove $n + 1 - m = 0$.
    have h_nm_eq_zero : n + 1 - m = 0 := by
      by_contra h
      have h_nm_positive : n + 1 - m > 0 := by omega
      have h_p_divides_n_or_nm : p ∣ n ∨ p ∣ n + 1 - m := (Nat.Prime.dvd_mul hp).mp h_p_divides_nm_term
      cases h_p_divides_n_or_nm with
      | inl h_p_div_n =>
        have h_n_ge_p : n ≥ p := Nat.le_of_dvd (by omega) h_p_div_n
        linarith
      | inr h_p_div_nm =>
        have h_nm_ge_p : n + 1 - m ≥ p := Nat.le_of_dvd h_nm_positive h_p_div_nm
        linarith
    -- Conclude $m = n + 1$.
    have h_m_eq_n1 : m = n + 1 := by nlinarith [h_nm_bound_lower, h_nm_eq_zero]
    exact h_m_eq_n1
  -- Substitute $m = n + 1$ to express $p = n^2 + n + 1$.
  have h_p_eq_n2n1 : p = n ^ 2 + n + 1 := by
    have h_p_nm : p = n * m + 1 := h_p_eq_nm_plus_one
    rw [h_m_eq_n_plus_one] at h_p_nm
    ring_nf at h_p_nm ⊢
    nlinarith
  -- Show $4p - 3 = (2n + 1)^2$.
  have h_4p_minus_3_eq_square : 4 * p - 3 = (2 * n + 1) ^ 2 := by
    rw [h_p_eq_n2n1]
    cases n with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => contradiction
      | succ n =>
        simp [Nat.mul_succ, Nat.pow_succ, Nat.add_assoc]
        ring_nf at *
        omega
  -- Conclude $4p - 3$ is a perfect square.
  have h_4p_minus_3_is_square : IsSquare (4 * p - 3) := by
    rw [h_4p_minus_3_eq_square]
    exact ⟨2 * n + 1, by ring⟩
  exact h_4p_minus_3_is_square
