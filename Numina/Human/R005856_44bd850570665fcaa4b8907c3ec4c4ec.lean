import Mathlib

/- Let $k$ be the answer to this problem.
The probability that an integer chosen uniformly at random from $\{1,2, \ldots, k\}$ is a multiple of 11 can be written as $\frac{a}{b}$
for relatively prime positive integers $a$ and $b$. Compute $100 a+b$. -/
theorem number_theory_610304 {k a b: ℕ}
  (co_ab: Nat.Coprime a b) (keq: k = 100*a + b)
  (apos: 0 < a) (bpos: 0 < b)
  (h: ( {n:ℕ | 11 ∣ n ∧ n ∈ Finset.Icc 1 k}.ncard: ℚ) /
    (Finset.Icc 1 k).card = a / b): 100 * a + b = 1000 := by

  -- let k = 11m + n.
  obtain ⟨m, n, rfl, hn⟩: ∃ (m n: ℕ), k = 11 * m + n ∧ n < 11 := by
    use (k/11),(k % 11)
    constructor
    · exact (Nat.div_add_mod k 11).symm
    . exact Nat.mod_lt k (by norm_num)

  -- then given probability condition simplifies to m / (11m+n) = a/b
  replace h: (m:ℚ) / (11*m+n) = a/b := by
    rw [← h]
    congr 1
    · norm_cast
      set f: (i:ℕ) → i < m → ℕ := fun i h => 11 * (i+1) with f_def
      symm
      apply Set.ncard_eq_of_bijective f ?_ ?_ ?_
      · intro i
        simp only [Finset.mem_Icc, Set.mem_setOf_eq,
        f_def, exists_prop, and_imp]
        rintro ⟨i, rfl⟩ ige ile
        use (i-1)
        constructor <;> omega
      · intro i h
        simp only [Finset.mem_Icc, f_def, Set.mem_setOf_eq,
        dvd_mul_right, true_and]
        constructor <;> omega
      · intro i j hi hj
        simp [f_def]
    · simp

  have hnz: 11*m + n ≠ 0 := by
    rintro heq
    simp only [keq, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or] at heq
    absurd heq; omega

  -- we find 11m + n ≠ 0, therefore can multiply denominators to the other side
  replace h: m * b = (11*m + n) * a := by
    qify
    qify at bpos hnz
    field_simp [bpos.ne', hnz] at h
    linarith only [h]

  -- b divide 11m + n, since b and a are coprime
  have bdvd: b ∣ 11*m + n := by
    have: b ∣ (11*m+n) * a := by
      rw [← h]
      exact Nat.dvd_mul_left b m
    refine Nat.Coprime.dvd_of_dvd_mul_right ?_ this
    exact Nat.coprime_comm.mp co_ab

  -- then b divide 100a + b, b divide 100 a. and a,b coprime, so b divide 100
  replace bdvd: b ∣ 100 := by
    rw [keq] at bdvd
    have: b ∣ 100*a := Nat.dvd_add_self_right.mp bdvd
    refine Nat.Coprime.dvd_of_dvd_mul_right ?_ this
    exact Nat.coprime_comm.mp co_ab

  -- m ≠ 0, otherwise a = 0
  have mnz: m ≠ 0 := by
    rintro heq
    have: (11*m+n) * a = 0 := by
      rw [← h, heq, zero_mul]
    simp only [mul_eq_zero, apos.ne', hnz, false_or] at this

  -- mb = (11m+n)a ≥ 11am, so b ≥ 11a ≥ 11
  have bge: b ≥ 11 := by
    have h1: m*b ≥ m*(11*a) := by
      rw [h]
      ring_nf
      simp
    have h2: b ≥ 11*a := by
      exact le_of_nsmul_le_nsmul_right mnz h1
    apply le_trans ?_ h2
    exact Nat.le_mul_of_pos_right 11 apos

  -- a divide b, since a divide mb and a,b coprime.
  have advd: a ∣ m := by
    have: a ∣ m*b := by
      rw [h]
      exact Nat.dvd_mul_left a (11 * m + n)
    exact Nat.Coprime.dvd_of_dvd_mul_right co_ab this

  -- then b > n, therefore 11m > 100a
  have hnb: n < b := by
    linarith only [hn, bge]
  -- a divide m, suppose m = aj. since m ≠ 0, also j ≠ 0
  rcases advd with ⟨j, rfl⟩
  have jnz: j ≠ 0 := by
    rintro rfl
    simp at mnz
  -- cancel a from both sides of h, simplifies to (b-11a)j = n < 11.
  replace h: (b - 11*a:ℤ) * j = n := by
    rw [mul_assoc a j b, mul_comm a _] at h
    simp only [mul_eq_mul_right_iff, apos.ne', or_false] at h
    zify at h
    linarith only [h]


  have haj: 100*a < (11*j)*a := by
    have: 100 * a + b < (11*j)*a + b := by
      rw [← keq, mul_comm a j, ← mul_assoc]
      simp [hnb]
    simpa using this
  replace haj: 100 < 11*j := by
    exact (Nat.mul_lt_mul_right apos).mp haj

  -- 100 < 11j, so j ≥ 10
  have hj: j ≥ 10 := by
    have: j > 9 := by linarith only [haj]
    exact this

  -- (b-11a) j = n < 11, then b-11a = 0 or = 1.
  have h': (b-11*a:ℤ) ≥ 0 := by
    have: (n:ℤ) ≥ 0 := by simp
    rw [← h] at this
    apply nonneg_of_mul_nonneg_left this ?_
    simp [Nat.zero_lt_of_ne_zero jnz]

  replace h: (b - 11*a: ℤ) ≤ 1 := by
    have: (b - 11*a: ℤ) * j ≤ 1 * j := by
      rw [h, one_mul]
      replace hn: n ≤ 10 := by exact Nat.le_of_lt_succ hn
      zify at hn hj
      apply hn.trans hj
    apply le_of_mul_le_mul_right this (by simp [Nat.zero_lt_of_ne_zero jnz])

  -- but a,b coprime. so if = 0, then must have a = 1.
  -- but then b = 11a = 1, contradiction to b divide 100.
  have: (b:ℤ) - 11*a ≠ 0 := by
    rintro heq
    replace heq: (b:ℤ) = 11*a := by
      linarith only [heq]
    norm_cast at heq
    rw [heq] at co_ab
    have: a.gcd (11*a) = a := by
      exact Nat.gcd_mul_left_right 11 a
    rw [co_ab] at this
    rw [← this, mul_one] at heq
    norm_num [heq] at bdvd

  -- therefore b = 11a+1
  have hba: b = 11*a + 1 := by
    zify
    replace: b - 11*a = (1:ℤ) := by
      omega
    linarith only [this]

  -- for 11a+1 divide 100, only solution is a=9
  have aeq: a = 9 := by
    rw [hba] at bdvd
    replace := Nat.le_of_dvd (by norm_num) bdvd
    replace: a ≤ 9 := by omega
    clear * - bdvd this apos
    revert bdvd apos
    decide +revert

  -- then b = 100, 100a+b = 1000
  norm_num [hba,aeq]