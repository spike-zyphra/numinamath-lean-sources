import Mathlib

/-Given that a , b, and c are natural numbers, and
2 ^ a * 3 ^ b * 7 ^ c = 1176, then the value of 2a+3b+7c is ?-/

theorem number_theory_634028 {a b c: ℕ} (h: 2 ^ a * 3 ^ b * 7 ^ c = 1176):
  2 * a + 3 * b + 7 * c = 23 := by

  -- we show a = 3
  have va: a = 3 := by
    have d: 2 ^ 3 ∣ 1176 := by
      norm_num
    rw [← h] at d

    -- show 3 ≤ a
    have s: 2 ^ 3 ∣ 2 ^ a := by
      rw [show 2 ^ a * 3 ^ b * 7 ^ c = 2 ^ a * (3 ^ b * 7 ^ c) by ring] at d
      apply Nat.Coprime.dvd_of_dvd_mul_right at d
      exact d
      apply Nat.Coprime.mul_right
      apply Nat.Coprime.pow
      norm_num
      apply Nat.Coprime.pow
      norm_num
    rw [Nat.pow_dvd_pow_iff_le_right] at s

    -- show a ≤ 3
    have t: 2 ^ a ∣ 1176 := by
      rw [← h]
      rw [show 2 ^ a * 3 ^ b * 7 ^ c = 2 ^ a * (3 ^ b * 7 ^ c) by ring]
      simp
    have r: 2 ^ a ∣ 2 ^ 3 := by
      rw [show 1176 = 2 ^ 3 * 147 by norm_num] at t
      apply Nat.Coprime.dvd_of_dvd_mul_right at t
      exact t
      rw [show 147 = 147 ^ 1 by norm_num]
      apply Nat.Coprime.pow
      norm_num
    rw [Nat.pow_dvd_pow_iff_le_right] at r
    linarith
    norm_num
    norm_num

  simp [va] at h
  replace h: 3 ^ b * 7 ^ c = 147 := by
    rw [show 8 * 3 ^ b * 7 ^ c = 8 * (3 ^ b * 7 ^ c) by ring] at h
    omega

  -- similar to a, we show b = 1
  have vb: b = 1 := by
    have d: 3 ^ 1 ∣ 147 := by
      norm_num
    rw [← h] at d

    -- show 1 ≤ b
    have s: 3 ^ 1 ∣ 3 ^ b := by
      apply Nat.Coprime.dvd_of_dvd_mul_right at d
      exact d
      apply Nat.Coprime.pow
      norm_num
    rw [Nat.pow_dvd_pow_iff_le_right] at s

    -- show b ≤ 1
    have t: 3 ^ b ∣ 147 := by
      rw [← h]
      simp
    have r: 3 ^ b ∣ 3 ^ 1 := by
      rw [show 147 = 3 ^ 1 * 49 by norm_num] at t
      apply Nat.Coprime.dvd_of_dvd_mul_right at t
      exact t
      rw [show 49 = 7 ^ 2 by norm_num]
      apply Nat.Coprime.pow
      norm_num
    rw [Nat.pow_dvd_pow_iff_le_right] at r
    linarith
    norm_num
    norm_num

  simp [vb] at h
  replace h: 7 ^ c = 7 ^ 2 := by omega
  rw [pow_right_inj₀] at h
  simp [va, vb, h]
  norm_num
  norm_num
  

