import Mathlib

/-
The proof idea is the same as in the original text:
1. From (3) and (4) we get `n + n^2 = 42`, i.e. `n * (n + 1) = 42`, from which we know `n = 6`.
2. Substitute back `p + q = 36`, and with `q = 36 - p`, combine `q > p` and `q - p < 10` to uniquely determine `p = 17`, `q = 19`, both of which are prime.
-/

theorem unique_prime_pair
  (p q n : ℕ)
  (hp : Prime p)
  (hq : Prime q)
  (hqgt : q > p)
  (hdiff : q - p < 10)
  (hsq : p + q = n ^ 2)
  (hsum : n + p + q = 42) :
  p = 17 ∧ q = 19 ∧ n = 6 := by
  -- From p + q = n^2 and n + p + q = 42, we get n + n^2 = 42
  have h_mul : n * (n + 1) = 42 := by
    calc
      n * (n + 1) = n + n ^ 2 := by ring
      _ = n + (p + q)     := by rw [←hsq]
      _ = 42              := by linarith [hsum]

  -- Determine n = 6
  have h_n : n = 6 := by
    -- Directly compute (6 : ℕ) * (6 + 1) = 42
    have h6 : (6 : ℕ) * (6 + 1) = 42 := by norm_num
    -- Prove this is the unique solution (by enumerating small values and excluding larger ones)
    by_cases h : n ≤ 6
    · interval_cases n
      · norm_num at h_mul
      · norm_num at h_mul
      · norm_num at h_mul
      · norm_num at h_mul
      · norm_num at h_mul
      · norm_num at h_mul
      · rfl
    · -- Case n > 6
      exfalso
      have : n ≥ 7 := by omega
      have : n * (n + 1) ≥ 7 * 8 := by
        apply Nat.mul_le_mul <;> omega
      norm_num at this
      linarith [h_mul]

  -- From n = 6, we get p + q = 36
  have h_pq : p + q = 36 := by
    calc p + q = n ^ 2 := hsq
    _ = 6 ^ 2 := by rw [h_n]
    _ = 36 := by norm_num

  -- Determine the range for p: 13 < p < 18
  have h_p_lower : 13 < p := by
    -- p > 13: derive from q - p < 10 and q = 36 - p
    have h_q : q = 36 - p := by omega
    calc p > (36 - 10) / 2 := by {
      have : q - p < 10 := hdiff
      rw [h_q] at this
      omega
    }
    _ = 13 := by norm_num

  have h_p_upper : p < 18 := by
    -- p < 18: derive from q > p and q = 36 - p
    have h_q : q = 36 - p := by omega
    calc p < 36 / 2 := by {
      have : q > p := hqgt
      rw [h_q] at this
      omega
    }
    _ = 18 := by norm_num

  -- From 13 < p < 18 and Prime p, we must have p = 17
  have h_p17 : p = 17 := by
    interval_cases p
    · -- p = 14: not prime (14 = 2 * 7)
      exfalso
      have h14 : 14 = 2 * 7 := by norm_num
      rw [h14] at hp
      exact Nat.not_prime_mul (by norm_num : 2 ≠ 1) (by norm_num : 7 ≠ 1) (Nat.prime_iff.mpr hp)
    · -- p = 15: not prime (15 = 3 * 5)
      exfalso
      have h15 : 15 = 3 * 5 := by norm_num
      rw [h15] at hp
      exact Nat.not_prime_mul (by norm_num : 3 ≠ 1) (by norm_num : 5 ≠ 1) (Nat.prime_iff.mpr hp)
    · -- p = 16: not prime (16 = 2 * 8)
      exfalso
      have h16 : 16 = 2 * 8 := by norm_num
      rw [h16] at hp
      exact Nat.not_prime_mul (by norm_num : 2 ≠ 1) (by norm_num : 8 ≠ 1) (Nat.prime_iff.mpr hp)
    · -- p = 17: indeed prime
      rfl

  -- From p + q = 36, we get q = 19
  have h_q19 : q = 19 := by
    linarith [h_pq, h_p17]

  exact ⟨h_p17, h_q19, h_n⟩