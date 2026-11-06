import Mathlib

/-E733 Let $k$ be a positive integer.
Determine the remainder of the Euclidean division of $2018^{2019^k}$ by 11.
Show that this remainder is 5 if $k$ is even, and 9 if $k$ is odd.-/

theorem number_theory_639116 (k: ℕ) (h: 0 < k): 2018 ^ (2019 ^ k) % 11 = if k % 2 = 0 then 5 else 9 := by

  set a:= 2019 ^ k
  rw [Nat.pow_mod]
  rw [show 2018 % 11 = 5 by simp]
  have c: 5 ^ 5 % 11 = 1 := by norm_num
  set q:= a / 5
  set r:= a % 5
  have d: a = 5 * q + r := by
    clear_value a
    omega
  have lr: r < 5 := by
    clear_value a
    omega
  rw [d]
  rw [Nat.pow_add]
  rw [Nat.mul_mod]
  have u: 5 ^ (5 * q) % 11 = 1 := by
    rw [Nat.pow_mul]
    rw [Nat.pow_mod]
    simp [c]
  simp [u]
  by_cases s: k % 2 = 0

  -- case k is even
  .
    simp [s]
    suffices r = 1 by
      simp [this]
    simp [r]
    simp [a]
    rw [Nat.pow_mod]
    simp
    apply Nat.dvd_of_mod_eq_zero at s
    apply exists_eq_mul_right_of_dvd at s
    obtain ⟨t, ht⟩ := s
    simp [ht]
    rw [Nat.pow_mul]
    simp
    rw [Nat.pow_mod]
    simp

  -- case k is odd
  .
    simp [s]
    suffices r = 4 by
      simp [this]
    simp [r, a]
    rw [Nat.pow_mod]
    simp
    simp at s
    replace s: (k + 1) % 2 = 0 := by
      rw [Nat.add_mod]
      simp [s]
    apply Nat.dvd_of_mod_eq_zero at s
    apply exists_eq_mul_right_of_dvd at s
    obtain ⟨t, ht⟩ := s
    have lt: 0 < t := by omega
    set q:= t - 1
    have h: k = 2 * q + 1 := by omega
    rw [h]
    ring_nf
    rw [Nat.mul_mod]
    rw [show q * 2 = 2 * q by omega]
    rw [Nat.pow_mul]
    rw [Nat.pow_mod]
    simp