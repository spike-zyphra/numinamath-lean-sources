import Mathlib

open Finset Real Nat
/-What is the smallest positive integer n which cannot be written in any of the following forms?
n=1+2+⋯+k for a positive integer
n=p ^ k for a prime number p and integer k
n=p+1 for a prime number p.-/
theorem number_theory_609335: IsLeast {n: ℕ | (1 ≤ n) ∧  ¬ ((∃ k: ℕ, (1 ≤ k) ∧ (n = ∑ i ∈ Icc 1 k,i))
∨ (∃ p k: ℕ, (1 ≤ p) ∧ (1 ≤ k) ∧ (Nat.Prime p) ∧ (n = p ^ k)) ∨ (∃ p: ℕ, n = p + 1 ∧ Nat.Prime p))} 22 := by

-- we first simplify the sum of natural numbers--
  have sum: ∀ n: ℕ, ∑ i ∈ Icc 1 n, i = (n * (n + 1)) / 2 := by
    intro n
    induction' n with n h
    . simp
    . simp [Finset.sum_Icc_succ_top]
      rw [show ∑ i ∈ Icc 1 n, i =  ∑ k ∈ Finset.Icc 1 n, k by simp] at h
      rw [h]
      rw [Mathlib.Tactic.Zify.natCast_eq]
      field_simp
      ring_nf
      omega

  constructor
  -- the forward direction --
  . constructor
    . omega
    . by_contra! h
      rcases h with h | h | h

      -- show that n ≠ 1 + 2 +... +k --
      . obtain ⟨k,hk⟩ := h
        rcases hk with ⟨hk, h⟩
        specialize sum k
        simp [sum] at h
        have eq: 2 * (k * (k + 1) / 2) = k * (k + 1) := by
          rw [show 2 * (k * (k + 1) / 2) = (k * (k + 1) / 2) * 2 by ring]
          rw [← Nat.dvd_iff_div_mul_eq]
          have case: 2 ∣ k ∨ 2 ∣ (k - 1) := by
            omega
          rcases case with h | h
          . apply exists_eq_mul_right_of_dvd at h
            obtain ⟨m,hm⟩ := h
            rw [hm]
            rw [show 2 * m * (2 * m + 1) = 2 * (m * (2 * m + 1)) by ring]
            omega
          . apply exists_eq_mul_right_of_dvd at h

            obtain ⟨m,hm⟩ := h
            replace hm: k = 2 * m + 1 := by
              omega
            rw [hm]
            have eq: (2 * m + 1) * (2 * m + 1 + 1) = 2 * ((2 * m  + 1) * (m + 1)) := by
              ring_nf
            simp [eq]
        replace h: 44 = k * (k + 1) := by
          calc
            44 = 2 * 22 := by norm_num
            _ = 2 *  (k * (k + 1)/2) := by rw [h]
            _ = k * (k + 1) := by rw [eq]
        have k1: k > 6 := by
          by_contra! k1
          nlinarith
        have k2: k < 8 := by
          by_contra! k2
          nlinarith
        have k3: k = 7 := by omega
        rw [k3] at h
        omega

      -- show that n ≠ p ^ k--
      . obtain ⟨p,k,h1⟩ := h
        rcases h1 with ⟨bp,bk,prime_p,h⟩
        by_cases hk: k = 1
        . rw [hk] at h
          simp at h
          rw [← h] at prime_p
          absurd prime_p
          norm_num
        . by_cases hk2: k = 2
          . simp [hk2] at h
            have bp1: p > 4 := by
              by_contra! bp1
              nlinarith
            have bp2: p < 4 := by
              by_contra! bp2
              nlinarith
            nlinarith
          . have bk3: 3 ≤ k := by omega
            have bp2: p < 3 := by
              by_contra! bp2
              have no: 27 ≤ 22 := by
                calc
                  27 = 3 ^ 3 := by norm_num
                   _ ≤ p ^ 3 := by apply Nat.pow_le_pow_of_le_left; omega
                   _ ≤ p ^ k := by apply Nat.pow_le_pow_of_le_right; omega; omega
                   _ = 22 := by rw[← h]
              tauto
            have p_val: p = 1 ∨ p = 2 := by omega
            rcases p_val with o | o
            . rw [o] at h
              simp at h
            . rw [o] at h
              have bk1: k < 5 := by
                by_contra! bk1
                have no: 32 ≤ 22 := by
                  calc
                    32 = 2 ^ 5 := by omega
                     _ ≤ 2 ^ k := by apply Nat.pow_le_pow_of_le_right; omega ;omega
                     _ = 22 := by omega
                tauto
              have k_val: k = 3 ∨ k = 4 := by omega
              rcases k_val with s | s
              . simp [s] at h
              . simp [s] at h

      -- show n ≠ p + 1 --
      . obtain ⟨p,hp⟩ := h
        simp at hp
        rcases hp with ⟨p1, p2⟩
        rw [p1] at p2
        absurd p2
        norm_num

  -- the backward direction --
  . intro n
    intro hn
    rcases hn with ⟨bn1,hn⟩
    by_contra! bn
    absurd hn
    replace hn: n ∈ Icc 0 21 := by
      simp [hn]
      omega
    fin_cases hn
    -- enumerate all possible values of n --
    . omega
  -- n = 1 --
    . left
      use 1
      constructor
      . omega
      . simp
    -- n = 2 --
    . right
      left
      use 2
      use 1
      simp
      norm_num
    --
    . right
      left
      use 3
      use 1
      simp
      norm_num
    -- n = 4 --
    . right
      left
      use 2
      use 2
      simp
      norm_num
    -- n = 5 --
    . right
      left
      use 5
      use 1
      simp
      norm_num
    -- n = 6 --
    . right
      right
      use 5
      norm_num
    -- n = 7 --
    . right
      left
      use 7
      use 1
      simp
      norm_num
    -- n = 8 --
    . right
      left
      use 2
      use 3
      simp
      norm_num
    -- n = 9 --
    . right
      left
      use 3
      use 2
      simp
      norm_num
    -- n = 10 --
    . left
      use 4
      simp
      simp [Finset.sum_Icc_succ_top]
    -- n = 11 --
    . right
      left
      use 11
      use 1
      simp
      norm_num
    -- n = 12 --
    . right
      right
      use 11
      norm_num
    -- n = 13 --
    . right
      left
      use 13
      use 1
      simp
      norm_num
    -- n = 14 --
    . right
      right
      use 13
      norm_num
    -- n = 15 --
    . left
      use 5
      simp [Finset.sum_Icc_succ_top]
    -- n = 16 --
    . right
      left
      use 2
      use 4
      simp
      norm_num
    -- n = 17 --
    . right
      left
      use 17
      use 1
      simp
      norm_num
    -- n = 18 --
    . right
      right
      use 17
      norm_num
    -- n = 19 --
    . right
      left
      use 19
      use 1
      simp
      norm_num
    -- n = 20 --
    . right
      right
      use 19
      norm_num
    -- n = 21 --
    . left
      use 6
      simp [Finset.sum_Icc_succ_top]