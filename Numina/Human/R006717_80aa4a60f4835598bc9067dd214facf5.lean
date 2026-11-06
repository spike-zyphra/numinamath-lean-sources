import Mathlib

/-Let $a$ and $b$ be non-negative integers, not both zero. Let $D$ be the number $2^a \cdot 5^b$.
Determine the smallest natural number $n$ such that $n$ is divisible by $D$ and the sum of its base-10 digits is $1$.
Show that the answer is $10^{\max(a,b)}$.-/

theorem number_theory_640491 (a b D: ℕ) (h0: a ≠ 0 ∨ b ≠ 0) (h1: D = 2 ^ a * 5 ^ b):
  IsLeast {n: ℕ | ∃ k: ℕ, n = 10 ^ k ∧ D ∣ n} (10 ^ (max a b)) := by

  constructor

  -- the forward direction
  .
    simp
    rw [h1]
    suffices 2 ^ a ∣ 10 ^ (max a b) ∧ 5 ^ b ∣ 10 ^ (max a b) by
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      .
        apply Nat.Coprime.pow
        norm_num
      .
        suffices s: 10 ^ a ∣ 10 ^ (max a b) by
          have u: 2 ^ a ∣ 10 ^ a := by
            by_cases o: a = 0
            .
              simp [o]
            .
              rw [Nat.pow_dvd_pow_iff]
              norm_num
              tauto
          apply dvd_trans u s
        apply Nat.pow_dvd_pow
        simp
      .
        suffices s: 10 ^ b ∣ 10 ^ (max a b) by
          have u: 5 ^ b ∣ 10 ^ b := by
            by_cases o: b = 0
            .
              simp [o]
            .
              rw [Nat.pow_dvd_pow_iff]
              norm_num
              tauto
          apply dvd_trans u s
        apply Nat.pow_dvd_pow
        simp
    by_cases o: a = 0 ∨ b = 0
    .
      rcases o with o | o
      .
        simp [o]
        simp [o] at h0
        rw [Nat.pow_dvd_pow_iff]
        norm_num
        omega
      .
        simp [o]
        simp [o] at h0
        rw [Nat.pow_dvd_pow_iff]
        norm_num
        omega

    constructor
    .
      suffices 2 ^ a ∣ 10 ^ a by
        have u: 10 ^ a ∣ 10 ^ (max a b) := by
          apply Nat.pow_dvd_pow
          simp
        apply dvd_trans this u
      rw [Nat.pow_dvd_pow_iff]
      norm_num
      omega
    .
      suffices 5 ^ b ∣ 10 ^ b by
        have u: 10 ^ b ∣ 10 ^ (max a b) := by
          apply Nat.pow_dvd_pow
          simp
        apply dvd_trans this u
      rw [Nat.pow_dvd_pow_iff]
      norm_num
      omega


  -- the backward direction
  .
    intro n h
    simp at h
    rcases h with ⟨s1, s2⟩
    obtain ⟨k, rfl⟩ := s1
    apply Nat.pow_le_pow_of_le_right
    .
      norm_num
    .
      simp
      rw [h1] at s2
      clear h1
      have h1: 2 ^ a ∣ 10 ^ k := by
        suffices 2 ^ a ∣ 2 ^ a * 5 ^ b by
          apply dvd_trans this s2
        simp
      have h2: 5 ^ b ∣ 10 ^ k := by
        suffices 5 ^ b ∣ 2 ^ a * 5 ^ b by
          apply dvd_trans this s2
        simp
      clear s2
      replace h1: 2 ^ a ∣ 2 ^ k := by
        rw [show 10 ^ k = 2 ^ k * 5 ^ k by rw [show 10 = 2 * 5 by norm_num]; rw [Nat.mul_pow]] at h1
        apply Nat.Coprime.dvd_of_dvd_mul_right at h1
        tauto
        apply Nat.Coprime.pow
        norm_num
      replace h2: 5 ^ b ∣ 5 ^ k := by
        rw [show 10 ^ k = 5 ^ k * 2 ^ k by rw [show 10 = 5 * 2 by norm_num]; rw [Nat.mul_pow]] at h2
        apply Nat.Coprime.dvd_of_dvd_mul_right at h2
        tauto
        apply Nat.Coprime.pow
        norm_num
      rw [Nat.pow_dvd_pow_iff_le_right] at h1 h2
      omega
      all_goals norm_num