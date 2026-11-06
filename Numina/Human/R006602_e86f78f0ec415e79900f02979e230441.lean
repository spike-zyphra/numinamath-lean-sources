import Mathlib

/-Let $k$ be a non-negative integer. The number $N = 4k+1$ is a positive integer.
Show that the unit digit of $2^N - 1$ is 1.-/

theorem number_theory_639037 (k N: ℕ) (h: N = 4 * k + 1): (2 ^ N - 1) % 10 = 1 := by

  zify
  set a:= 2 ^ N
  have la: 2 ≤ a := by
    simp [a]
    nth_rewrite 1 [show 2 = 2 ^ 1 by simp]
    apply Nat.pow_le_pow_right
    omega
    omega
  have f: ↑(a - 1) = (a - (1: ℤ)) := by
    apply Int.natCast_sub
    simp [a]
    apply Nat.pow_pos
    omega
  rw [f]
  clear f
  rw [Int.sub_emod]
  rw [show 1 % 10 = (1: ℤ) by simp]
  suffices a % 10 = 2 by
    zify at this
    simp [this]
  simp [a]
  rw [Nat.pow_mod]
  rw [show 2 % 10 = 2 by simp]
  suffices (2 ^ N - 2) % 10 = 0 by
    rw [show 2 ^ N = 2 + (2 ^ N - 2) by omega]
    rw [Nat.add_mod]
    simp [this]
  apply Nat.mod_eq_zero_of_dvd
  suffices 2 ∣2 ^ N - 2 ∧ 5 ∣ 2 ^ N - 2 by
    rw [show 10 = 2 * 5 by simp]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    norm_num
    tauto
    tauto
  constructor
  .
    apply Nat.dvd_sub
    .
      omega
    .
      rw [show N = N - 1 + 1 by omega]
      ring_nf
      simp
    .
      norm_num
  .
    simp [h]
    ring_nf
    rw [show k * 4 = 4 * k by omega]
    rw [Nat.pow_mul]
    suffices 5 ∣  (2 ^ 4) ^ k * 2 + 3 by
      rw [show (2 ^ 4) ^ k * 2 - 2 = (2 ^ 4) ^ k * 2 + 3 - 5 by omega]
      apply Nat.dvd_sub
      .
        omega
      .
        tauto
      .
        simp
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod]
    suffices (2 ^ 4) ^ k % 5 = 1 by
      rw [Nat.mul_mod]
      rw [this]
    rw [show 2 ^ 4 = 16 by simp]
    rw [Nat.pow_mod]
    simp