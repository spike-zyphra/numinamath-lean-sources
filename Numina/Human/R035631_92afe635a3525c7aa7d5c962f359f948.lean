import Mathlib

/- The numbers $p$ and $q$ are prime and satisfy

$$
\frac{p}{p+1}+\frac{q+1}{q}=\frac{2 n}{n+2}
$$

for some positive integer $n$. Find all possible values of $q-p$.
Origin. Luxembourg (Pierre Haas). -/
theorem number_theory_606123: {x: ℤ | ∃ p q n: ℤ, (x = (q: ℤ) - p) ∧ (Prime p) ∧ (Prime q)
∧ (0 < n) ∧ (0 < p) ∧ (0 < q) ∧  (p / (p + 1 : ℚ) + (q + 1) / q = 2 * n / (n + 2 : ℚ))} = {2, 3 ,5} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor

 -- the forward direction
  . intro h
    simp
    obtain ⟨p, q, n, hx, prime_p, prime_q, hn, hp, hq, h⟩ := h
    replace hp: 2 ≤ p := by
      by_contra! no
      interval_cases p
      all_goals absurd prime_p; norm_num
    replace hq: 2 ≤ q := by
      by_contra! no
      interval_cases q
      all_goals absurd prime_q; norm_num

    -- we first simplify the equation
    replace h: 2 * q * n * (p + 1) - (n + 2) * (2 * p * q + p + q + 1) = 0 := by
      qify
      have ne: (q: ℚ) ≠ 0 := by
        simp
        omega
      field_simp at h
      replace h: (2: ℚ) * ↑n * ((↑p + 1) * ↑q) - (↑p * ↑q + (↑q + 1) * (↑p + 1)) * (↑n + 2) = 0 := by
        rw [h]
        ring
      have o: (2: ℚ) * ↑q * ↑n * (↑p + 1) - (↑n + 2) * (2 * ↑p * ↑q + ↑p + ↑q + 1)
       = (2: ℚ) * ↑n * ((↑p + 1) * ↑q) - (↑p * ↑q + (↑q + 1) * (↑p + 1)) * (↑n + 2) := by ring
      rw [o]
      exact h
    replace h: 2 * q * n * (p + 1) = (n + 2) * (2 * p * q + p + q + 1) := by linarith
    by_contra! x_ne

    -- we show that 3 ≤ p
    replace hp: 3 ≤ p := by
      by_contra! p_val
      replace p_val: p = 2 := by omega
      simp [p_val] at *
      clear hp prime_p p_val
      simp [hx] at x_ne
      have dq: q ∣ n + 2 := by
        have o: q ∣ 2 * q * n * 3 := by
          rw [show 2 * q * n * 3 = q * (2 * n * 3) by ring]
          apply Int.dvd_mul_right
        rw [h] at o
        apply IsCoprime.dvd_of_dvd_mul_right at o
        exact o
        rw [show 4 * q + 2 + q + 1 = 5 * q + 3 by ring]
        have i: IsCoprime q ((5 * q + 3) + -5 * q) := by
          ring_nf
          rw [Int.isCoprime_iff_gcd_eq_one]
          rw [Int.gcd_eq_natAbs]
          simp
          rw [← Nat.Coprime.gcd_eq_one]
          apply Nat.Coprime.symm
          rw [Nat.Prime.coprime_iff_not_dvd]
          by_contra! d3
          rw [Nat.Prime.dvd_iff_eq] at d3
          zify at d3
          rw [show |q| = q by apply abs_of_nonneg; omega] at d3
          simp [d3] at h
          nlinarith
          rw [← Int.prime_iff_natAbs_prime ]
          exact prime_q
          norm_num
          norm_num
        rw [IsCoprime.add_mul_right_right_iff] at i
        exact i
      apply exists_eq_mul_right_of_dvd at dq
      obtain ⟨k, dq⟩ := dq
      simp [dq] at h
      replace h: 6 * n = k * (5 * q + 3) := by nlinarith
      replace dq: n = q * k - 2 := by linarith
      simp [dq] at h
      ring_nf at h
      replace h: (q - 3) * k = 12 := by nlinarith
      have o: q - 3 ∣ 12 := by
        have j: q - 3 ∣ (q - 3) * k := by
          apply Int.dvd_mul_right
        rw [h] at j
        exact j
      rw [← Int.natAbs_dvd_natAbs] at o
      simp at o
      apply Nat.le_of_dvd at o
      zify at o
      replace o: q ≤ 15 := by
        have i: q - 3 ≤ |q - 3| := by apply le_abs_self
        linarith
      interval_cases q
      <;> absurd prime_q
      all_goals norm_num
      all_goals omega

    -- we show that 3 ≤ q
    replace hq: 3 ≤ q := by
      by_contra! q_val
      replace q_val: q = 2 := by omega
      simp [q_val] at *
      clear hq prime_q q_val
      have eq: n = p * n + 10 * p + 6 := by nlinarith
      nlinarith

    -- we show that p and q are odd
    have oddp: Odd p := by
      by_contra! t
      simp at t
      apply Even.natAbs at t
      rw [Nat.Prime.even_iff] at t
      have s: p ≤ ↑p.natAbs := by
        apply Int.le_natAbs
      have r: (3: ℤ) ≤ p.natAbs := by
        linarith
      rw [t] at r
      tauto
      rw [← Int.prime_iff_natAbs_prime]
      exact prime_p
    have oddq: Odd q := by
      by_contra! t
      simp at t
      apply Even.natAbs at t
      rw [Nat.Prime.even_iff] at t
      have s: q ≤ ↑q.natAbs := by
        apply Int.le_natAbs
      have r: (3: ℤ) ≤ q.natAbs := by
        linarith
      rw [t] at r
      tauto
      rw [← Int.prime_iff_natAbs_prime]
      exact prime_q
    have d2: 2 ∣ n + 2 := by
      have o: 2 ∣ 2 * q * n * (p + 1) := by
        rw [show 2 * q * n * (p + 1) = 2 * (q * n * (p + 1)) by ring]
        apply dvd_mul_right
      rw [h] at o
      apply IsCoprime.dvd_of_dvd_mul_right at o
      exact o
      rw [Int.isCoprime_iff_gcd_eq_one]
      have i: Int.gcd 2 (2 * p * q + p + q + 1) ∣ 1 := by
        rw [Int.gcd_dvd_iff]
        have l: 2 ∣ p + q := by
          rw [← even_iff_two_dvd]
          rw [Int.even_add']
          simp [oddp, oddq]
        apply exists_eq_mul_right_of_dvd at l
        obtain ⟨k, l⟩ := l
        rw [show 2 * p * q + p + q + 1 = 2 * p * q + (p + q) + 1 by ring]
        rw [l]
        use - p * q - k
        use 1
        ring
      apply Nat.eq_one_of_dvd_one i
    replace d2: 2 ∣ n := by omega
    apply exists_eq_mul_right_of_dvd at d2
    obtain ⟨k, hk⟩ := d2
    simp [hk] at h
    replace h: 2 * q * k * (p + 1) = (k + 1) * (2 * p * q + p + q + 1) := by nlinarith

    -- similarly, we have 2 ∣ k + 1
    have d2: 2 ∣ k + 1 := by
      have o: 2 ∣ 2 * q * k * (p + 1) := by
        rw [show 2 * q * k * (p + 1) = 2 * (q * k * (p + 1)) by ring]
        apply dvd_mul_right
      rw [h] at o
      apply IsCoprime.dvd_of_dvd_mul_right at o
      exact o
      rw [Int.isCoprime_iff_gcd_eq_one]
      have i: Int.gcd 2 (2 * p * q + p + q + 1) ∣ 1 := by
        rw [Int.gcd_dvd_iff]
        have l: 2 ∣ p + q := by
          rw [← even_iff_two_dvd]
          rw [Int.even_add']
          simp [oddp, oddq]
        apply exists_eq_mul_right_of_dvd at l
        obtain ⟨k, l⟩ := l
        rw [show 2 * p * q + p + q + 1 = 2 * p * q + (p + q) + 1 by ring]
        rw [l]
        use - p * q - k
        use 1
        ring
      apply Nat.eq_one_of_dvd_one i
    apply exists_eq_mul_right_of_dvd at d2
    obtain ⟨l, hl⟩ := d2
    replace hl: k = 2 * l - 1 := by omega
    simp [hl] at h
    replace h: q * (2 * l - 1) * (p + 1) = l * (2 * p * q + p + q + 1) := by nlinarith

    -- we simplify h by expanding
    replace h: q * l = (q + l) * (p + 1) := by
      have o: q * l - (q + l) * (p + 1) = 0 := by
        have j: q * (2 * l - 1) * (p + 1) - l * (2 * p * q + p + q + 1) = 0 := by linarith
        have i: q * l - (q + l) * (p + 1) = q * (2 * l - 1) * (p + 1) - l * (2 * p * q + p + q + 1) := by
          ring_nf
        rw [j] at i
        exact i
      linarith

    -- we show that q ∣ l
    have dl: q ∣ l := by
      by_contra! d1
      have s: IsCoprime q l := by
        have d2: ¬ q.natAbs ∣ l.natAbs := by
          by_contra! d2
          rw [Int.natAbs_dvd_natAbs] at d2
          tauto
        rw [← Nat.Prime.coprime_iff_not_dvd] at d2
        rw [show q = |q| by symm; apply abs_of_nonneg; omega]
        rw [show l = |l| by symm; apply abs_of_nonneg; omega]
        rw [Int.isCoprime_iff_gcd_eq_one]
        apply Nat.Coprime.gcd_eq_one at d2
        rw [show |q| = ↑q.natAbs by symm;apply Int.natCast_natAbs]
        rw [show |l| = ↑l.natAbs by symm;apply Int.natCast_natAbs]
        rw [Int.gcd_natCast_natCast]
        exact d2
        rw [← Int.prime_iff_natAbs_prime ]
        exact prime_q
      have o: q + l ∣ q * l := by
        have j: q + l ∣ (q + l) * (p + 1) := by
          apply Int.dvd_mul_right
        rw [←h] at j
        exact j
      apply IsCoprime.dvd_of_dvd_mul_right at o
      have nl: 1 ≤ l := by omega
      apply exists_eq_mul_right_of_dvd at o
      obtain ⟨z, o⟩ := o
      have l1: 0 < q := by omega
      have l2: 0 < q + l := by omega
      have lz: 0 < z := by nlinarith
      nlinarith
      rw [show q + l = |q + l| by symm; apply abs_of_nonneg; omega]
      nth_rewrite 2 [show l = |l| by symm; apply abs_of_nonneg; omega]
      have v: |q + l| = |q| + |l| := by
        rw [abs_add_eq_add_abs_iff]
        omega
      rw [v]
      have j: IsCoprime (|q| + 1 * |l|) |l| := by
        rw [IsCoprime.add_mul_right_left_iff]
        rw [show |q| = q by apply abs_of_nonneg; omega]
        rw [show |l| = l by apply abs_of_nonneg; omega]
        exact s
      simp at j
      exact j
    apply exists_eq_mul_right_of_dvd at dl
    obtain ⟨s, ds⟩ := dl
    simp [ds] at h
    replace h: q * s = (s + 1) * (p + 1) := by nlinarith

    -- we show that s ∣ p + 1
    have ds: s ∣ p + 1 := by
      have o: s ∣ q * s := by
        apply Int.dvd_mul_left
      rw [h] at o
      apply IsCoprime.dvd_of_dvd_mul_left at o
      exact o
      have f: IsCoprime s (s + 1 + s * (-1)) := by
        simp
        apply isCoprime_one_right
      apply IsCoprime.of_add_mul_left_right at f
      exact f
    apply exists_eq_mul_right_of_dvd at ds
    obtain ⟨t, dt⟩ := ds
    simp [dt] at h
    replace h: q = (s + 1) * t:= by nlinarith
    have ns: 1 ≤ s := by nlinarith
    have dq: s + 1 ∣ q := by
      rw [h]
      apply Int.dvd_mul_right
    rw [← Int.natAbs_dvd_natAbs] at dq
    rw [Nat.Prime.dvd_iff_eq] at dq
    zify at dq
    rw [show |q| = q by apply abs_of_nonneg; omega] at dq
    rw [show |s + 1| = s + 1 by apply abs_of_nonneg; omega] at dq
    simp [dq] at h
    replace h: t = 1 := by nlinarith
    simp [h] at dt
    rw [← dt] at dq
    replace dq: q - p = 2 := by nlinarith
    rw [← hx] at dq
    simp [dq] at x_ne
    rw [← Int.prime_iff_natAbs_prime]
    exact prime_q
    omega


  -- the backward direction
  . intro h
    simp at h
    rcases h with h | h | h
    -- case 1: x = 2
    . use 3
      use 5
      use 78
      simp
      norm_num
      simp [h]
    -- case 2: x = 3
    . use 2
      use 5
      use 28
      simp
      norm_num
      simp [h]
    -- case 3: x = 5
    . use 2
      use 7
      use 19
      simp
      norm_num
      simp [h]