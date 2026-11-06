import Mathlib

/- Vind alle paren priemgetallen $(p, q)$ waarvoor er positieve gehele $(m, n)$ bestaan zodat

$$
(p+q)^{m}=(p-q)^{n}
$$ -/

theorem number_theory_605746: {(p, q): ℤ × ℤ | 0 < p ∧ 0 < q ∧ Prime p ∧ Prime q ∧
   ∃ m n: ℕ, 0 < m ∧ 0 < n ∧ (p + q) ^ m = (p - q) ^ n} = {(3, 5), (5, 3)} := by

   ext ⟨p, q⟩
   constructor
    -- the forward direction
   .
    intro h
    simp at h
    simp
    rcases h with ⟨hp, hq, pp, pq, ⟨m, hm, n, hn, h⟩⟩

    have ne: p ≠ q := by -- we see that p ≠ q
      by_contra! no
      simp [no] at h
      rw [show (0: ℤ) ^ n = 0 by apply zero_pow; omega] at h
      apply pow_eq_zero at h
      replace h: q = 0 := by omega
      simp [h] at hq
    have ne2: |p - q| ≠ 1 := by
      by_contra! o
      replace h: |p + q| ^ m = |p - q| ^ n := by
        rw [pow_abs]
        rw [pow_abs]
        rw [h]
      simp [o] at h
      rw [pow_eq_one_iff_of_nonneg] at h
      rw [show |p + q| = p + q by apply abs_of_nonneg; omega] at h
      omega
      apply abs_nonneg
      omega

    -- then we show the their gcd is at most 2
    have g: (p + q).gcd (p - q) ∣ 2 := by
      rw [Int.gcd_dvd_iff]
      have i: p.gcd q = 1 := by
        rw [Int.gcd_eq_natAbs]
        apply Nat.Coprime.gcd_eq_one
        rw [Nat.Prime.coprime_iff_not_dvd]
        by_contra! v
        rw [Nat.prime_dvd_prime_iff_eq] at v
        zify at v
        rw [show |p| = p by apply abs_of_nonneg; omega] at v
        rw [show |q| = q by apply abs_of_nonneg; omega] at v
        tauto
        all_goals rw [← Int.prime_iff_natAbs_prime]; trivial
      replace i: p.gcd q ∣ 1 := by
        rw [i]
      rw [Int.gcd_dvd_iff] at i
      obtain ⟨x, y, j⟩ := i
      use (x + y)
      use (x - y)
      replace j: ↑(2: ℕ) = 2 * (p * x + q * y) := by
        rw [← j]
        simp
      rw [j]
      ring

    -- then combine g and h, we see that one is 2 and another is power of 2
    have f: |p - q| = 2 ∧ ∃ k: ℕ, p + q = 2 ^ k := by
      replace ne: p - q ≠ 0 := by omega
      -- for convenience, we need to turn it in ℕ
      set a:= p - q
      set b:= p + q
      set x:= a.natAbs with hx
      set y:= b.natAbs with hy
      have f: x = 2 ∧ ∃ k: ℕ, y = 2 ^ k := by
        rw [Int.gcd_eq_natAbs] at g
        rw [← hx,← hy] at g
        replace h: y ^ m = x ^ n := by
          simp [x,y]
          zify
          rw [← abs_pow]
          rw [← abs_pow]
          rw [h]
        replace ne: x ≠ 0 := by
          simp [x]
          tauto
        have ne2: x ≠ 1 := by
          simp [x]
          zify
          tauto
        have lx: 2 ≤ x := by omega
        have ly: 4 ≤ y := by
          simp [y]
          zify
          rw [show |b| = b by apply abs_of_nonneg; omega]
          simp [b]
          have l1: 2 ≤ p := by
            by_contra! no
            replace no: p = 1 := by omega
            simp [no] at pp
          have l2: 2 ≤ q := by
            by_contra! no
            replace no: q = 1 := by omega
            simp [no] at pq
          nlinarith
        clear * - ly lx h g hn hm
        clear_value a b
        clear_value x y
        have g':= g
        apply Nat.le_of_dvd at g
        replace g: y.gcd x = 0 ∨ y.gcd x = 1 ∨ y.gcd x = 2 := by omega
        rcases g with g | g | g
        .
          simp [g] at g'
        .
          clear g'
          rw [← Nat.coprime_iff_gcd_eq_one] at g
          replace g: (y ^ m).Coprime x := by
            apply Nat.Coprime.pow_left
            exact g
          have eq: x ^ n = x * x ^ (n - 1) := by
              nth_rewrite 1 [show n = n - 1 + 1 by omega]
              ring
          have d: y ^ m ∣ x ^ n := by rw [h]
          rw [eq] at d
          have s:= Nat.Coprime.dvd_of_dvd_mul_left g d
          apply Nat.le_of_dvd at s
          rw [h] at s
          rw [Nat.pow_le_pow_iff_right] at s
          omega
          omega
          have o: 1 ≤ x ^ (n - 1) := by
            apply Nat.one_le_pow
            omega
          omega
        .
          clear g'
          have dy: 2 ∣ y := by
            rw [← g]
            apply Nat.gcd_dvd_left
          have dx: 2 ∣ x := by
            rw [← g]
            apply Nat.gcd_dvd_right
          apply exists_eq_mul_right_of_dvd at dx
          obtain ⟨x',ix⟩ := dx
          apply exists_eq_mul_right_of_dvd at dy
          obtain ⟨y',iy⟩ := dy
          rw [ix, iy] at g
          rw [Nat.gcd_mul_left] at g
          replace g: y'.gcd x' = 1 := by omega
          simp [ix,iy] at *
          have t: (y' ^ m).Coprime (x' ^ n) := by
            apply Nat.Coprime.pow_left
            apply Nat.Coprime.pow_right
            exact g
          have o: y' ∣ 2 ^ n := by
            have o1: y' ^ m ∣ (2 * y') ^ m := by
              rw [show (2 * y') ^ m = 2 ^ m * y' ^ m by ring]
              simp
            rw [h] at o1
            rw [show (2 * x') ^ n = 2 ^ n * x' ^ n by ring] at o1
            have o2: y' ^ m ∣ 2 ^ n := by
              apply Nat.Coprime.dvd_of_dvd_mul_right t o1
            have o3: y' ∣ y' ^ m := by
              have eq: y' ^ m = y' * y' ^ (m - 1) := by
                nth_rewrite 1 [show m = m - 1 + 1 by omega]
                ring
              rw [eq]
              simp
            apply dvd_trans o3 o2
          rw [Nat.dvd_prime_pow] at o
          obtain ⟨s, hs⟩ := o
          rcases hs with ⟨ls, hs⟩
          rw [hs]
          have o: x' ∣ 2 ^ m := by
            have o1: x' ^ n ∣ (2 * x') ^ n := by
              rw [show (2 * x') ^ n = 2 ^ n * x' ^ n by ring]
              simp
            rw [← h] at o1
            rw [show (2 * y') ^ m = 2 ^ m * y' ^ m by ring] at o1
            have o2: x' ^ n ∣ 2 ^ m := by
              apply Nat.Coprime.symm at t
              apply Nat.Coprime.dvd_of_dvd_mul_right t o1
            have o3: x' ∣ x' ^ n := by
              have eq: x' ^ n = x' * x' ^ (n - 1) := by
                nth_rewrite 1 [show n = n - 1 + 1 by omega]
                ring
              rw [eq]
              simp
            apply dvd_trans o3 o2
          rw [Nat.dvd_prime_pow] at o
          obtain ⟨t, ht⟩ := o
          rcases ht with ⟨lt, ht⟩
          rw [ht]
          simp [ht,hs] at g h
          have it: t = 0 := by
            by_contra! it
            replace it: 1 ≤ t := by omega
            have o1: 2 ∣ 2 ^ t := by
              nth_rewrite 1 [show 2 = 2 ^ 1 by ring]
              rw [Nat.pow_dvd_pow_iff_le_right]
              exact it
              norm_num
            have o2: 2 ∣ 2 ^ s := by
              nth_rewrite 1 [show 2 = 2 ^ 1 by ring]
              rw [Nat.pow_dvd_pow_iff_le_right]
              by_contra! no
              replace no: s= 0 := by omega
              simp [no] at hs
              simp [hs] at ly
              norm_num
            have c: 2 ∣ (2 ^ s).gcd (2 ^ t) := by
              apply Nat.dvd_gcd
              exact o2
              exact o1
            rw [g] at c
            omega
          simp [it]
          use (s + 1)
          ring
          norm_num
          norm_num
        norm_num

      simp [x,y] at f
      zify at f
      rw [show |b| = b by apply abs_of_nonneg; omega] at f
      exact f

  -- then we can use the fact above to derive p and q
    rcases f with ⟨l, r⟩
    obtain ⟨k, r⟩:= r
    by_cases e: p < q
    -- case p < q
    .
      left
      rw [show |p - q| =- (p - q) by apply abs_of_nonpos; omega] at l
      replace l: q = p + 2 := by omega
      simp [l] at r
      have o: 3 ∣ p ∨ 3 ∣ p + 1 ∨ 3 ∣ p + 2 := by
        omega
      rcases o with o | o | o
      -- case p % 3 = 0
      .
        rw [← Int.natAbs_dvd_natAbs] at o
        simp at o
        rw [Nat.prime_dvd_prime_iff_eq] at o
        zify at o
        rw [show |p| = p by apply abs_of_nonneg; omega] at o
        simp [o]
        omega
        norm_num
        rw [← Int.prime_iff_natAbs_prime]
        exact pp
      -- case p % 3 = 1
      .
        have i: (3: ℤ) ∣ 2 ^ k := by
          rw [← r]
          rw [show p + (p + 2)= 2 * (p + 1) by ring]
          have j: p + 1 ∣ 2 * (p + 1) := by simp
          apply dvd_trans o j
        have i3: Prime (3: ℤ) := by norm_num
        have j:= Prime.dvd_of_dvd_pow i3 i
        tauto
      -- case p % 3 = 2
      .
        rw [← l] at o
        rw [← Int.natAbs_dvd_natAbs] at o
        simp at o
        rw [Nat.prime_dvd_prime_iff_eq] at o
        zify at o
        rw [show |q| = q by apply abs_of_nonneg; omega] at o
        simp [← o] at l
        replace l: p = 1 := by omega
        simp [l] at pp
        norm_num
        rw [← Int.prime_iff_natAbs_prime]
        exact pq
    -- case p > q, similar as above
    .
      replace e: q < p := by omega
      right
      rw [show |p - q| = (p - q) by apply abs_of_nonneg; omega] at l
      replace l: p = q + 2 := by omega
      simp [l] at r
      have o: 3 ∣ q ∨ 3 ∣ q + 1 ∨ 3 ∣ q + 2 := by
        omega
      rcases o with o | o | o
      -- case q % 3 = 0
      .
        rw [← Int.natAbs_dvd_natAbs] at o
        simp at o
        rw [Nat.prime_dvd_prime_iff_eq] at o
        zify at o
        rw [show |q| = q by apply abs_of_nonneg; omega] at o
        simp [o]
        omega
        norm_num
        rw [← Int.prime_iff_natAbs_prime]
        exact pq
      -- case q % 3 = 1
      .
        have i: (3: ℤ) ∣ 2 ^ k := by
          rw [← r]
          rw [show (q + 2) + q= 2 * (q + 1) by ring]
          have j: q + 1 ∣ 2 * (q + 1) := by simp
          apply dvd_trans o j
        have i3: Prime (3: ℤ) := by norm_num
        have j:= Prime.dvd_of_dvd_pow i3 i
        tauto
      -- case q % 3 = 2
      .
        rw [← l] at o
        rw [← Int.natAbs_dvd_natAbs] at o
        simp at o
        rw [Nat.prime_dvd_prime_iff_eq] at o
        zify at o
        rw [show |p| = p by apply abs_of_nonneg; omega] at o
        simp [← o] at l
        replace l: q = 1 := by omega
        simp [l] at pq
        norm_num
        rw [← Int.prime_iff_natAbs_prime]
        exact pp


  -- the backward direction
   intro h
   simp at h
   rcases h with h | h
   .
      simp [h]
      norm_num
      use 2
      norm_num
      use 6
      norm_num
   .
      simp [h]
      norm_num
      use 2
      norm_num
      use 6
      norm_num