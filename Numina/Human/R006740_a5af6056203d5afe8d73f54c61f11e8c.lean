import Mathlib

open Finset Real Nat

/-For any integer K≥6, the last two digits of the product
∏ i ∈ Icc 1 K, (2 ^ i + 1) are 75.-/

theorem number_theory_640673 (K: ℕ) (h: 6 ≤ K): (∏ i ∈ Icc 1 K, (2 ^ i + 1)) % 100 = 75 := by

  -- prove by induction on K
  induction' K with n ih
  .
    simp at h
  .
    by_cases l: n = 5
    .
      simp [l]
      repeat simp [Finset.prod_Icc_succ_top]
    .
      replace h: 6 ≤ n := by omega
      clear l
      simp [h] at ih
      rw [Finset.prod_Icc_succ_top]
      rw [Nat.mul_mod]
      rw [ih]
      clear ih
      set x:= (2 ^ (n + 1) + 1) % 100
      have lx: 1 ≤ x := by
        suffices x ≠ 0 by omega
        by_contra! o
        simp [x] at o
        apply Nat.dvd_of_mod_eq_zero  at o
        replace o: 2 ∣ 2 ^ (n + 1) + 1 := by
          have c: 2 ∣ 100 := by norm_num
          apply dvd_trans c o
        have c: 2 ∣ 1 := by
          rw [show 1 = 2 ^ (n + 1) + 1 - 2 ^ (n + 1) by omega]
          apply Nat.dvd_sub
          .
            omega
          .
            tauto
          .
            ring_nf
            simp
        norm_num at c
      suffices (75 * x - 75) % 100 = 0 by
        rw [show 75 * x = 75 * x - 75 + 75 by omega]
        rw [Nat.add_mod]
        rw [show 75 % 100 = 75 by norm_num]
        simp [this]
      apply Nat.mod_eq_zero_of_dvd
      rw [show 100 = 25 * 4 by norm_num]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      .
        norm_num
      .
        rw [show 75 * x - 75 = 25 * (3 * (x - 1)) by omega]
        simp
      .

        suffices 4 ∣ x - 1 by
          have u: x - 1 ∣ 75 * x - 75 := by
            rw [show 75 * x - 75 = 75 * (x - 1) by omega]
            simp
          apply dvd_trans this u
        simp [x]
        suffices 4 ∣ (2 ^ (n + 1) + 1) % 100 + 3 by
          rw [show (2 ^ (n + 1) + 1) % 100 - 1 = (2 ^ (n + 1) + 1) % 100 + 3 - 4 by omega]
          apply Nat.dvd_sub
          omega
          tauto
          simp
        apply Nat.dvd_of_mod_eq_zero
        rw [Nat.add_mod]
        rw [show 3 % 4 = 3 by norm_num]
        rw [Nat.mod_mod_of_dvd]
        suffices (2 ^ (n + 1) + 1) % 4 = 1 by simp [this]
        rw [Nat.add_mod]
        suffices 2 ^ (n + 1) % 4 = 0 by
          simp [this]
        rw [show n + 1 = n - 1 + 2 by omega]
        ring_nf
        rw [Nat.mul_mod]
        rw [show 4 % 4 = 0 by norm_num]
        simp
        norm_num

      omega

