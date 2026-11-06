import Mathlib

-- we show a simp lemma about factorization in ℕ
lemma lemma_1 {n: ℕ} (h: 0 < n): (n - 1) * (n + 1) = n ^ 2 - 1 := by
  zify
  have o1: ↑(n - 1) = ↑n - (1: ℤ) := by
    apply Int.natCast_sub
    omega
  rw [o1]
  clear o1
  have o2: ↑(n ^ 2 - (1: ℕ)) = ↑n ^ 2 - (1: ℤ) := by
    apply Int.natCast_sub
    nlinarith
  rw [o2]
  clear o2
  ring

-- we prove the simp case of Bernoulli's inequality
lemma lemma_2 (k x: ℕ) (hk: 1 < k) (hx: 0 < x): x ^ k + 1 < (x + 1) ^ k := by
  -- prove by induction
  induction' k with k ih
  .
    simp at hk
  .
    by_cases l: k ≤ 1
    .
      have o: k = 0 ∨ k = 1 := by omega
      rcases o with o | o
      .
        simp [o] at hk
      .
        simp [o]
        ring_nf
        omega
    .
      simp at l
      simp [l] at ih
      rw [show (x + 1) ^ (k + 1) = (x + 1) * (x + 1) ^ k by ring]
      have l1: (x + 1) * (x ^ k + 1) < (x + 1) * (x + 1) ^ k := by
        nlinarith
      have l2: x ^ (k + 1) + 1 < (x + 1) * (x ^ k + 1) := by
        ring_nf
        omega
      linarith


/-Let n,m and k be positive integers satisfying
(n−1)n(n+1)=m ^ k
 Prove that k=1.-/

theorem number_theory_238713 {k m n: ℕ} (hk: 0 < k) (hn: 0 < n) (hm: 0 < m)
  (h: (n - 1) * n * (n + 1) = m ^ k): k = 1 := by

  -- firstly, we show that both n and (n-1) * (n + 1) are k-th powers
  rw [show (n - 1) * n * (n + 1) = (n - 1) * (n + 1) * n by ring] at h
  have l:= h
  apply exists_eq_pow_of_mul_eq_pow at h
  .
    obtain ⟨m1, h⟩ := h
    have lm1: 0 < m1 := by
      by_contra! o
      replace o: m1 = 0 := by omega
      simp [o] at h
      rw [show 0 ^ k = 0 by apply Nat.zero_pow_of_pos; omega] at h
      simp at h
      replace h: n = 1 := by omega
      simp [h] at l
      symm at l
      rw [Nat.pow_eq_zero] at l
      simp [l] at hm
    simp [h] at l
    have d: m1 ^ k ∣ m ^ k := by
      rw [← l]
      simp
    rw [Nat.pow_dvd_pow_iff (by omega)] at d
    apply exists_eq_mul_right_of_dvd at d
    obtain ⟨c, s⟩ := d
    simp [s] at l
    rw [show (m1 * c) ^ k = m1 ^ k * c ^ k by ring] at l
    have o: 0 < m1 ^ k := by
      apply Nat.pos_pow_of_pos
      by_contra! t
      replace t: m1 = 0 := by omega
      simp [t] at s
      omega
    replace l: n = c ^ k := by
      apply Nat.mul_left_cancel at l
      exact l
      exact o
    clear s
    clear o
    rw [lemma_1] at h
    simp [l] at h

    -- we prove by contradiction
    by_contra! r
    replace r: 2 ≤ k := by omega

    -- we show contradiction from h
    rw [show (c ^ k) ^ 2 = (c ^ 2) ^ k by ring] at h
    set p:= c ^ 2
    have o: 0 < p ^ k := by
      apply Nat.pos_pow_of_pos
      by_contra! o
      replace o: p = 0 := by omega
      simp [p] at o
      simp [o] at l
      rw [show 0 ^ k = 0 by apply Nat.zero_pow_of_pos; omega] at l
      simp [l] at hn
    have s: m1 ^ k < p ^ k := by
      rw [← h]
      omega
    replace h: p ^ k = m1 ^ k + 1 := by
      rw [← h]
      omega
    rw [Nat.pow_lt_pow_iff_left (by omega)] at s
    set q:= p - m1
    have lq: 0 < q := by
      omega
    have hq: p = m1 + q := by
      omega
    simp [hq] at h
    clear hq o
    clear_value q
    have d: (m1 + q) ^ k % q = (m1 ^ k + 1) % q := by
      rw [h]
    rw [Nat.pow_mod] at d
    rw [Nat.add_mod] at d
    rw [show q % q = 0 by apply Nat.mod_self] at d
    norm_num at d
    rw [Nat.add_mod] at d
    nth_rewrite 2 [Nat.pow_mod] at d

    -- then we must have q = 1
    have lq: q = 1 := by
      by_contra! o
      rw [show 1 % q = 1 by rw [Nat.one_mod_eq_one]; omega] at d
      set t:= (m1 % q) ^ k % q
      have f: q ∣ (t + 1) - ((t + 1) % q) := by
        apply Nat.dvd_sub_mod
      rw [← d] at f
      rw [show t + 1 - t = 1 by omega] at f
      apply Nat.le_of_dvd at f
      omega
      norm_num

    -- finally, we use q = 1 to show contradiction
    clear d
    simp [lq] at h
    clear lq

    -- use lemma_2, we see that left side of h is more than right side
    have f:= lemma_2 k m1 (by omega) (by omega)
    rw [h] at f
    simp at f
    omega

  -- show the coprime relation
  .
    simp
    apply Nat.Coprime.gcd_eq_one
    apply Nat.Coprime.mul
    .
      rw [Nat.coprime_self_sub_left]
      apply Nat.coprime_one_left
      omega
    .
      rw [Nat.coprime_self_add_left ]
      apply Nat.coprime_one_left
      
