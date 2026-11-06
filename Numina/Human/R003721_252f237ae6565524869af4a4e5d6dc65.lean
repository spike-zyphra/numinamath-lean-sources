import Mathlib

/-A natural number ends with zero, and the greatest of its divisors,
not equal to itself -/

theorem number_theory_210109 (n d: ℕ) (hn: 0 < n) (h1: n % 10 = 0) (h2: d ∣ n) (h3: d ≠ n) (h4: ∀ c, c ∣ n → c ≤ d)
  (h5: ∃ p m, Nat.Prime p ∧ 0 < m ∧ d = p ^ m):
  n % 100 = 10 ∨ n % 100 = 50 := by

  -- we first show that d is indeed n / 2
  apply Nat.dvd_of_mod_eq_zero at h1
  set r:= n / 2
  have eq: n = 2 * r := by
    simp [r]
    rw [Nat.mul_div_cancel']
    have u: 2 ∣ 10 := by norm_num
    apply dvd_trans u h1
  have hr: d = r := by
    specialize h4 r
    have dr: r ∣ n := by
      simp [eq]
    simp [dr] at h4
    apply exists_eq_mul_right_of_dvd at h2
    obtain ⟨q, hq⟩ := h2
    have lq: 2 ≤ q := by
      suffices q ≠ 0 ∧ q ≠ 1 by omega
      constructor
      .
        by_contra! o
        simp [o] at hq
        omega
      .
        by_contra! o
        simp [o] at hq
        omega
    simp [eq] at hq
    have u: d ≤ r := by nlinarith
    omega

  simp [hr] at *
  clear h3 h4
  obtain ⟨p, hp, m, hm, h⟩ := h5
  simp [eq] at *
  clear_value r
  clear hr eq h2
  replace h1: 5 ∣ r := by omega
  rw [h] at h1
  apply Nat.Prime.dvd_of_dvd_pow (by norm_num) at h1
  rw [Nat.prime_dvd_prime_iff_eq (by norm_num) (by tauto)] at h1
  symm at h1
  simp [h1] at h
  rw [h]
  clear * - hm
  by_cases l: m = 1
  .
    simp [l]
  .
    right
    replace l: 2 ≤ m := by omega
    clear hm
    have l0: 25 ≤ 5 ^ m := by
      rw [show m = m - 2 + 2 by omega]
      ring_nf
      suffices 0 < 5 ^ (m - 2) by
        omega
      apply Nat.pow_pos
      omega
    have l1: 50 ≤ 2 * 5 ^ m := by
      omega
    suffices (2 * 5 ^ m - 50) % 100 = 0 by
      set v:= 2 * 5 ^ m
      rw [show v = v - 50 + 50 by omega]
      rw [Nat.add_mod]
      simp [this]
    apply Nat.mod_eq_zero_of_dvd
    rw [show 100 = 2 * 50 by norm_num]
    rw [show 2 * 5 ^ m - 50 = 2 * (5 ^ m - 25) by omega]
    apply Nat.mul_dvd_mul_left
    suffices 25 ∣ 5 ^ m - 25 ∧ 2 ∣ 5 ^ m - 25 by
      rw [show 50 = 25 * 2 by norm_num]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      norm_num
      tauto
      tauto
    constructor
    .
      rw [show m = m - 2 + 2 by omega]
      ring_nf
      rw [show 5 ^ (m - 2) * 25 - 25 = 25 * (5 ^ (m - 2) - 1) by omega]
      simp
    .
      apply Even.two_dvd
      rw [Nat.even_sub']
      suffices Odd (5 ^ m) ∧ Odd 25 by
        tauto
      constructor
      .
        apply Odd.pow
        decide
      .
        decide
      exact l0