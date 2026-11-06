import Mathlib

/-434 Let $N$ be a positive integer whose last two digits are 32.
Determine the last two digits of $N^N$. Show the answer is 76. -/

theorem number_theory_635752 (N: ℕ) (h: N % 100 = 32): N ^ N % 100 = 76 := by

  rw [Nat.pow_mod]
  rw [h]
  have l: 32 ≤ N := by
    by_contra! o
    rw [Nat.mod_eq_of_lt] at h
    omega
    linarith
  have l1: 76 ≤ 32 ^ N := by
    suffices 32 ^ 2 ≤ 32 ^ N by
      clear l
      linarith
    apply Nat.pow_le_pow_right
    norm_num
    linarith
  suffices (32 ^ N - 76) % 100 = 0 by
    rw [show 32 ^ N = 76 + (32 ^ N - 76) by omega]
    rw [Nat.add_mod]
    rw [this]
  apply Nat.mod_eq_zero_of_dvd
  suffices 4 ∣ 32 ^ N - 76 ∧ 25 ∣ 32 ^ N - 76 by
    rw [show 100 = 4 * 25 by norm_num]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    norm_num
    tauto
    tauto
  constructor
  .
    rw [show N = N - 1 + 1 by omega]
    ring_nf
    rw [show 32 ^ (N - 1) * 32 - 76 = 4 * (8 * 32 ^ (N - 1) - 19) by omega]
    simp
  .
    suffices 25 ∣ 32 ^ N + 24 by
      rw [show 32 ^ N - 76 = 32 ^ N + 24 - 100 by omega]
      apply Nat.dvd_sub
      .
        omega
      .
        tauto
      .
        norm_num
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod]
    suffices 32 ^ N % 25 = 1 by
      simp [this]
    rw [Nat.pow_mod]
    rw [show 32 % 25 = 7 by norm_num]
    replace h: N % 4 = 0 := by
      rw [show N % 4 = N % 100 % 4 by omega]
      simp [h]
    apply Nat.dvd_of_mod_eq_zero at h
    apply exists_eq_mul_right_of_dvd at h
    obtain ⟨k, hk⟩ := h
    rw [hk]
    rw [Nat.pow_mul]
    rw [Nat.pow_mod]
    simp