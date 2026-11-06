import Mathlib

/-E579 Let $K$ be a positive integer. Prove that $2^{3^{K-1}}+1$ is divisible by $3^K$.-/

theorem number_theory_637273 (K: ℕ) (h: 0 < K): 3 ^ K ∣ 2 ^ (3 ^ (K - 1)) + 1 := by

  induction' K with n ih
  .
    simp
  .
    by_cases s: n = 0
    .
      simp [s]
    .
      replace h: 0 < n := by
        omega
      clear s
      simp [h] at ih
      rw [show n + 1 - 1 = n - 1 + 1 by omega]
      ring_nf
      rw [Nat.pow_mul]
      set a:= 3 ^ (n - 1)
      set b:= 2 ^ a
      zify
      rw [show (1: ℤ) + b ^ 3 = (1 + b) * (1 - b + b ^ 2) by ring]
      suffices (3: ℤ) ∣ 1 - b + b ^ 2 by
        zify at ih
        apply Int.mul_dvd_mul
        .
          rw [show (1: ℤ) + b = b + 1 by ring]
          tauto
        .
          tauto
      rw [show (1: ℤ) - b + b ^ 2 = (b + 1) ^ 2 - 3 * b by ring]
      apply Int.dvd_sub
      .
        zify at ih
        replace ih: 3 ∣ b + (1: ℤ) := by
          suffices 3 ∣ 3 ^ n by
            zify at this
            apply dvd_trans this ih
          rw [show n = n - 1 + 1 by omega]
          ring_nf
          simp
        have u: (b + (1: ℤ)) ∣ (b + (1: ℤ)) ^ 2 := by
          rw [show (b + (1: ℤ)) ^ 2 = (b + (1: ℤ)) * (b + (1: ℤ)) by ring]
          simp
        apply dvd_trans ih u

      simp