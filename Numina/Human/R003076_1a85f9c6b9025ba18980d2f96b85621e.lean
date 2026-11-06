import Mathlib

-- we show two simp lemmas that will be used in the main theorem
lemma lemma_1 (p1 p2: ℤ) (lp1: 0 < p1) (lp2: 0 < p2) (ne: p1 ≠ p2) (hp1: Prime p1) (hp2: Prime p2):
  p1 * p2 ≠ 1000 := by
  -- for convenience, we first turn the integers into natural numbers
  by_contra! h
  set p:= p1.natAbs
  set q:= p2.natAbs
  replace hp1: Nat.Prime p := by
    simp [p]
    rw [← Int.prime_iff_natAbs_prime ]
    tauto
  replace hp2: Nat.Prime q := by
    simp [q]
    rw [← Int.prime_iff_natAbs_prime ]
    tauto
  replace h: p * q = 1000 := by
    simp [p, q]
    rw [← Int.natAbs_mul]
    simp [h]
  replace ne: p ≠ q := by
    simp [p, q]
    zify
    rw [show |p1| = p1 by apply abs_of_pos lp1]
    rw [show |p2| = p2 by apply abs_of_pos lp2]
    tauto
  clear_value p q
  have d1: 5 ∣ p * q := by
    rw [h]
    norm_num
  rw [Nat.Prime.dvd_mul] at d1
  rcases d1 with d | d
  .
    rw [Nat.prime_dvd_prime_iff_eq] at d
    symm at d
    simp [d] at h
    replace h: q = 200 := by omega
    simp [h] at hp2
    norm_num at hp2
    norm_num
    tauto
  .
    rw [Nat.prime_dvd_prime_iff_eq] at d
    symm at d
    simp [d] at h
    replace h: p = 200 := by omega
    simp [h] at hp1
    norm_num at hp1
    norm_num
    tauto
  norm_num

lemma lemma_2 (p1 p2: ℤ) (lp1: 0 < p1) (lp2: 0 < p2) (ne: p1 ≠ p2) (hp1: Prime p1) (hp2: Prime p2):
  ¬ 9 ∣ p1 * p2 := by
  -- for convenience, we first turn the integers into natural numbers
  by_contra! h
  set p:= p1.natAbs
  set q:= p2.natAbs
  replace hp1: Nat.Prime p := by
    simp [p]
    rw [← Int.prime_iff_natAbs_prime ]
    tauto
  replace hp2: Nat.Prime q := by
    simp [q]
    rw [← Int.prime_iff_natAbs_prime ]
    tauto
  replace h: 9 ∣ p * q := by
    simp [p, q]
    rw [← Int.natAbs_mul]
    rw [show 9 = (9: ℤ).natAbs by norm_num]
    rw [Int.natAbs_dvd_natAbs]
    tauto
  replace ne: p ≠ q := by
    simp [p, q]
    zify
    rw [show |p1| = p1 by apply abs_of_pos lp1]
    rw [show |p2| = p2 by apply abs_of_pos lp2]
    tauto
  clear_value p q
  have d: 3 ∣ p * q := by
    have o: 3 ∣ 9 := by norm_num
    apply dvd_trans o h
  rw [Nat.Prime.dvd_mul] at d
  rcases d with d | d
  .
    rw [Nat.prime_dvd_prime_iff_eq] at d
    symm at d
    simp [d] at h
    replace h: 3 ∣ q := by
      omega
    rw [Nat.prime_dvd_prime_iff_eq] at h
    simp [h] at d
    tauto
    norm_num
    tauto
    norm_num
    tauto
  .
    rw [Nat.prime_dvd_prime_iff_eq] at d
    symm at d
    simp [d] at h
    replace h: 3 ∣ p := by
      omega
    rw [Nat.prime_dvd_prime_iff_eq] at h
    simp [h] at d
    tauto
    norm_num
    tauto
    norm_num
    tauto
  norm_num


/-We are looking for a natural number n with a four-digit decimal representation, which has the following properties:
1.Its cross sum is an odd square number.
2.It is the product of exactly two different prime numbers.
3.The sum of the two prime numbers is ten times the number obtained by removing the units digit and the tens digit from the number n.
4.The difference between one prime factor and ten times the other is equal to
the number obtained by removing the hundreds digit and the thousands digit from the number n.-/

theorem number_theory_151154: {n: ℤ | ∃ a b c d, 1 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧ 0 ≤ c ∧ c ≤ 9 ∧ 0 ≤ d ∧ d ≤ 9 ∧
  n = a * 1000 + b * 100 + c * 10 + d ∧ (∃ m, Odd m ∧ a + b + c + d = m ^ 2) ∧
  (∃ p1 p2, 0 < p1 ∧ 0 < p2 ∧ Prime p1 ∧ Prime p2 ∧ p1 ≠ p2 ∧ n = p1 * p2 ∧ p1 + p2 = 10 * (a * 10 + b) ∧ p2 - 10 * p1 = 10 * c + d)}
  = {1969} := by

  ext n
  constructor

  -- the forward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨a, b, c, d, la, ra, lb, rb, lc, rc, ld, rd, hn, h1, h2⟩ := h
    obtain ⟨p1, p2, lp1, lp2, hp1, hp2, ne, h2, h3, h4⟩ := h2
    obtain ⟨m, hm, h1⟩ := h1
    set f:= |m|
    rw [show m ^ 2 = f ^ 2 by simp [f]] at h1
    have lf: 0 ≤ f := by
      apply abs_nonneg
    have hf: Odd f := by
      simp [f]
      rw [odd_abs]
      tauto
    clear hm
    clear_value f
    simp

    -- we first show that f = 5, then a + b + c + d = 25
    have vf: f = 5 := by
      by_contra! i
      have rf: f < 7 := by
        clear *- ra rb rc rd h1
        nlinarith
      interval_cases f
      all_goals absurd hf; try decide
      .
        simp at h1
        have va: a = 1 := by
          clear * - la lb lc ld h1
          omega
        simp [va] at h1
        have vb: b = 0 := by omega
        have vc: c = 0 := by omega
        have vd: d = 0 := by omega
        simp [va, vb, vc, vd] at hn
        simp [hn] at h2
        symm at h2
        absurd h2
        exact lemma_1 p1 p2 lp1 lp2 ne hp1 hp2
      .
        simp at h1
        have dn: 9 ∣ n := by
          rw [hn]
          rw [show a * 1000 + b * 100 + c * 10 + d = 9 * (111 * a + 11 * b + c) + (a + b + c + d) by ring]
          apply dvd_add
          .
            simp
          .
            simp [h1]
        rw [h2] at dn
        absurd dn
        exact lemma_2 p1 p2 lp1 lp2 ne hp1 hp2
      .
        simp at i

    simp [vf] at h1
    clear lf vf hf

    -- then we show that p1 = 11
    have v: p1 = 11 := by
      rw [show a * 1000 + b * 100 + c * 10 + d = 10 * (10 * (a * 10 + b)) + (10 * c + d) by omega] at hn
      simp [h2, ← h3, ← h4] at hn
      ring_nf at hn
      clear *- hn lp1 lp2
      nlinarith

    simp [v] at *
    clear lp1 hp1
    have dn: 11 ∣ n := by
      rw [h2]
      simp
    replace dn: 11 ∣ -a + b - c + d := by
      rw [show -a + b - c + d = a * 1000 + b * 100 + c * 10 + d - 11 * (91 * a + 9 * b + c) by ring]
      apply dvd_sub
      .
        rw [← hn]
        exact dn
      .
        simp
    apply exists_eq_mul_right_of_dvd at dn
    obtain ⟨k, hk⟩ := dn
    have lk: k ≤ 1 := by
      clear * - hk ra rb rc rd la lb lc ld
      nlinarith
    have rk: -1 ≤ k := by
      clear * - hk ra rb rc rd la lb lc ld
      nlinarith
    interval_cases k

    -- k = -1
    .
      simp at hk
      have f1: a + c = 18 := by
        clear *- h1 hk
        omega
      have f2: b + d = 7 := by
        clear *- h1 hk
        omega
      clear h1 hk
      have va: a = 9 := by
        clear * - f1 f2 ra rc
        omega
      have vc: c = 9 := by
        clear * - f1 f2 ra rc
        omega
      simp [va, vc] at *
      replace h3: p2 = 10 * b + 889 := by
        clear * - h3
        omega
      replace h4: p2 = d + 200 := by
        clear * - h4
        omega
      rw [h4] at h3
      have lb: b ≤ 7 := by
        omega
      interval_cases b
      all_goals omega

    -- k = 0
    .
      simp at hk
      clear *- h1 hk
      omega

    -- k = 1
    .
      simp at hk
      have f1: a + c = 7 := by
        clear *- h1 hk
        omega
      have f2: b + d = 18 := by
        clear *- h1 hk
        omega
      clear h1 hk
      have vb: b = 9 := by
        clear * - f1 f2 rb rd lb ld
        omega
      have vd: d = 9 := by
        clear * - f1 f2 rb rd lb ld
        omega
      simp [vb, vd] at *
      replace h4: p2 = 119 + 10 * c := by
        clear * - h4
        omega
      simp [h4] at h3
      ring_nf at h3
      replace h3: 10 * a - c = 4 := by
        clear * - h3
        omega
      have sa: a ≤ 7 := by
        omega
      interval_cases a
      all_goals omega


  -- the backward direction
  .
    intro h
    simp at h
    simp only [Set.mem_setOf_eq, h]
    use 1, 9, 6, 9
    norm_num
    constructor
    .
      use 5
      decide
    .
      use 11
      norm_num
      use 179
      norm_num
