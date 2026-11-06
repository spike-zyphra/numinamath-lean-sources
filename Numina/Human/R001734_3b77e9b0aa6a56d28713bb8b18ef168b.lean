import Mathlib

-- we first show that if n is odd, then 5 divides 2^n + 3^n
lemma lemma_1 (n: ℕ) (h: Odd n): 5 ∣ (2 ^ n + 3 ^ n) := by
    set q:= n / 4
    set r:= n % 4  -- it suffices to check n % 4

    -- then r = 1 or 3
    have hr: r = 1 ∨ r = 3 := by
      suffices i: r ≠ 0 ∧ r ≠ 2 by
        omega
      by_contra! j
      have k: 2 ∣ r := by omega
      simp [r] at k
      apply Nat.mod_eq_zero_of_dvd at k
      rw [Nat.mod_mod_of_dvd] at k
      apply Nat.dvd_of_mod_eq_zero at k
      rw [← even_iff_two_dvd] at k
      absurd h
      simp [k]
      norm_num
    have hq: q * 4 + r = n := by omega
    have s1: 2 ^ n = 16 ^ q * 2 ^ r := by
      simp [← hq]
      ring_nf
      rw [show q * 4 = 4 * q by omega]
      rw [Nat.pow_mul]
      simp
      ring
    have s2: 3 ^ n = 81 ^ q * 3 ^ r := by
      simp [← hq]
      ring_nf
      rw [show q * 4 = 4 * q by omega]
      rw [Nat.pow_mul]
      simp
      ring
    simp [s1, s2]
    clear s1 s2
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod]
    have f1: (16 ^ q * 2 ^ r) % 5 = (2 ^ r) % 5 := by
      rw [Nat.mul_mod]
      rw [Nat.pow_mod]
      simp
    have f2: (81 ^ q * 3 ^ r) % 5 = (3 ^ r) % 5 := by
      rw [Nat.mul_mod]
      rw [Nat.pow_mod]
      simp
    rw [f1, f2]
    clear f1 f2
    -- we check all possible cases for r = 1 or 3
    rcases hr with r1 | r3
    .
      simp [r1]
    .
      simp [r3]

-- we show that if 25 divides 2^n + 3^n, then n % 20 = 5 or n % 20 = 15
lemma lemma_2 (n: ℕ) (h: 25 ∣ 2 ^ n + 3 ^ n): n % 20 = 5 ∨ n % 20 = 15 := by
  set q:= n / 20
  set r:= n % 20  -- it suffices to check n % 20, since φ(25) = 20

  have lr: r < 20 := by omega
  have s: n = 20 * q + r := by omega
  have s1: 2 ^ n = (2 ^ 20) ^ q * 2 ^ r := by
    rw [s]
    rw [Nat.pow_add]
    rw [Nat.pow_mul]
  have s2: 3 ^ n = (3 ^ 20) ^ q * 3 ^ r := by
    rw [s]
    rw [Nat.pow_add]
    rw [Nat.pow_mul]
  apply Nat.mod_eq_zero_of_dvd at h
  rw [Nat.add_mod] at h
  rw [s1, s2] at h
  clear s1 s2
  have f1: (2 ^ 20) ^ q * 2 ^ r % 25 = 2 ^ r % 25 := by
    rw [Nat.mul_mod]
    suffices (2 ^ 20) ^ q % 25 = 1 by
      rw [this]
      simp
    rw [Nat.pow_mod]
    simp
  have f2: (3 ^ 20) ^ q * 3 ^ r % 25 = 3 ^ r % 25 := by
    rw [Nat.mul_mod]
    suffices (3 ^ 20) ^ q % 25 = 1 by
      rw [this]
      simp
    rw [Nat.pow_mod]
    simp
  rw [f1, f2] at h
  clear f1 f2
  clear_value r
  clear s

  -- then we can check all possible cases for n % 20
  interval_cases r
  all_goals norm_num at h
  .
    left
    rfl
  .
    right
    rfl


/- Prove that for any prime number $p$ the equation $2^p+3^p=a^n$ has no solution $(a,n)$ in integers greater than $1$. -/
theorem number_theory_29964 (p : ℕ) (hp : Nat.Prime p) :
    ¬∃ a n : ℕ, a > 1 ∧ n > 1 ∧ 2^p + 3^p = a^n := by

    by_contra! h
    obtain ⟨a, n, ha, hn, h⟩ := h
    by_cases l: 5 < p

    -- case 1: 5 < p
    .
      have o: Odd p := by
        apply Nat.Prime.odd_of_ne_two
        tauto
        omega
      have d5:= lemma_1 p o
      rw [h] at d5

      -- then we obtain 5 ∣ a, hence 25 ∣ a ^ n
      apply Nat.Prime.dvd_of_dvd_pow (by norm_num) at d5
      have d: 25 ∣ a ^ n := by
        rw [show n = n - 2 + 2 by omega]
        ring_nf
        have f: 25 ∣ a ^ 2 := by
          rw [show 25 = 5 ^ 2 by norm_num]
          rw [Nat.pow_dvd_pow_iff]
          tauto
          norm_num
        have g: a ^ 2 ∣ a ^ 2 * a ^ (n - 2) := by
          simp
        apply dvd_trans f g
      rw [← h] at d

      -- apply lemma_2 to obtain 5 ∣ p
      have j:= lemma_2 p d
      replace j: 5 ∣ p := by
        apply Nat.dvd_of_mod_eq_zero
        rw [show p % 5 = p % 20 % 5 by symm; apply Nat.mod_mod_of_dvd; norm_num]
        rcases j with j | j
        .
          simp [j]
        .
          simp [j]

      -- then p = 5, which is a contradiction
      rw [Nat.prime_dvd_prime_iff_eq] at j
      omega

      norm_num
      tauto


    -- case 2: p ≤ 5, we check one by one
    .
      simp at l
      interval_cases p
      all_goals norm_num at hp

      -- p = 2
      .
        simp at h
        have u: a ∣ 13 := by
          rw [h]
          rw [show n = n - 1 + 1 by omega]
          ring_nf
          simp
        apply Nat.Prime.eq_one_or_self_of_dvd (by norm_num) at u
        rcases u with u | u
        .
          omega
        .
          simp [u] at h
          replace h: 13 ^ 1 = 13 ^ n := by rw [← h]; omega
          rw [pow_right_inj₀] at h
          omega
          norm_num
          norm_num

      -- p = 3
      .
        simp at h
        have u: 7 ∣ a := by
          suffices 7 ∣ a ^ n by
            apply Nat.Prime.dvd_of_dvd_pow at this
            tauto
            norm_num
          rw [← h]
          norm_num
        have v: 5 ∣ a := by
          suffices 5 ∣ a ^ n by
            apply Nat.Prime.dvd_of_dvd_pow at this
            tauto
            norm_num
          rw [← h]
          norm_num
        have c: 35 ∣ a := by
          rw [show 35 = 5 * 7 by norm_num]
          apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) v u
        rw [h] at c
        nth_rewrite 2 [show a = a ^ 1 by ring] at c
        rw [Nat.pow_dvd_pow_iff_le_right] at c
        omega
        tauto

      -- p = 5
      .
        simp at h
        have u: 11 ∣ a := by
          suffices 11 ∣ a ^ n by
            apply Nat.Prime.dvd_of_dvd_pow at this
            tauto
            norm_num
          rw [← h]
          norm_num
        replace u: 121 ∣ a ^ n := by
          suffices 121 ∣ a ^ 2 by
            have o: a ^ 2 ∣ a ^ n := by
              rw [show n = n - 2 + 2 by omega]
              ring_nf
              simp
            apply dvd_trans this o
          rw [show 121 = 11 ^ 2 by norm_num]
          rw [Nat.pow_dvd_pow_iff]
          tauto
          norm_num
        rw [← h] at u
        norm_num at u
