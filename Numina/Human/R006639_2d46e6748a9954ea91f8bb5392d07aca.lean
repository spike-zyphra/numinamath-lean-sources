import Mathlib

/- lemma from latest mathlib, named `Nat.lcm_eq_iff`.  -/
theorem l_lcm_eq_iff {n m l : Nat} :
    Nat.lcm n m = l ↔ n ∣ l ∧ m ∣ l ∧ (∀ c, n ∣ c → m ∣ c → l ∣ c) := by
  refine ⟨?_, fun ⟨hn, hm, hl⟩ => Nat.dvd_antisymm (lcm_dvd hn hm) ?_⟩
  · rintro rfl
    exact ⟨dvd_lcm_left _ _, dvd_lcm_right _ _, fun _ => Nat.lcm_dvd⟩
  · exact hl _ (dvd_lcm_left _ _) (dvd_lcm_right _ _)

/- definition of lcm  -/
lemma l_lcm_eq_mul_div (m n : Nat) : Nat.lcm m n = m * n / Nat.gcd m n := rfl

/- if b and c are coprime, then lcm (ab, c) = lcm (a,c) × b  -/
lemma l_lcm_eq_lcm_mul_of_coprime {a b c: ℕ}
  (hbc: Nat.Coprime b c):
  (a*b).lcm c = (a.lcm c) * b := by
  rw [l_lcm_eq_mul_div, hbc.gcd_mul_right_cancel]
  have h1: a*b*c = (a*c) * b := by ring
  have h2: (a*b*c)/(a.gcd c) = (a*c / (a.gcd c)) * b := by
    rw [h1]
    rw [mul_comm (a*c) b, Nat.mul_div_assoc, mul_comm b _]
    suffices a.gcd c ∣ a by
      exact Dvd.dvd.mul_right this c
    exact Nat.gcd_dvd_left a c
  rw [h2, ← l_lcm_eq_mul_div]

/- for prime number p,q, lcm (p^m1 q^n1, p^m2 q^n2) = p^(max m1 m2) q^(max n1 n2) -/
lemma l_lcm_prime_pow_mul {p q m1 m2 n1 n2: ℕ}
  (pp: Nat.Prime p) (pq: Nat.Prime q) (pneq: p ≠ q):
  (p^m1 * q^n1).lcm (p^m2 * q^n2) = p^(max m1 m2) * q^(max n1 n2) := by
  rw [l_lcm_eq_iff]
  split_ands
  · refine Nat.mul_dvd_mul ?_ ?_
    · exact Nat.pow_dvd_pow p (Nat.le_max_left m1 m2)
    · exact Nat.pow_dvd_pow q (Nat.le_max_left n1 n2)
  · refine Nat.mul_dvd_mul ?_ ?_
    · exact Nat.pow_dvd_pow p (Nat.le_max_right m1 m2)
    · exact Nat.pow_dvd_pow q (Nat.le_max_right n1 n2)
  · intro c h1 h2
    by_cases hc: c = 0
    · simp [hc]
    · have := Nat.exists_eq_pow_mul_and_not_dvd hc p pp.ne_one
      rcases this with ⟨i, d, h3, ceq⟩
      have dnz: d ≠ 0 := by
        rw [ceq] at hc
        exact Nat.ne_zero_of_mul_ne_zero_right hc
      have := Nat.exists_eq_pow_mul_and_not_dvd dnz q pq.ne_one
      rcases this with ⟨j, e, h4, deq⟩
      have h5: ¬ p ∣ e := by
        contrapose! h3
        rw [deq]
        exact Dvd.dvd.mul_left h3 (q ^ j)
      have co1: Nat.Coprime (p^m1 * q^n1) e := by
        refine Nat.Coprime.mul ?_ ?_
        <;> refine Nat.Coprime.pow_left _ ?_
        · exact (Nat.Prime.coprime_iff_not_dvd pp).mpr h5
        · exact (Nat.Prime.coprime_iff_not_dvd pq).mpr h4
      have co2: Nat.Coprime (p^m2 * q^n2) e := by
        refine Nat.Coprime.mul ?_ ?_
        <;> refine Nat.Coprime.pow_left _ ?_
        · exact (Nat.Prime.coprime_iff_not_dvd pp).mpr h5
        · exact (Nat.Prime.coprime_iff_not_dvd pq).mpr h4
      rw [ceq, deq, ← mul_assoc, co1.dvd_mul_right] at h1
      rw [ceq, deq, ← mul_assoc, co2.dvd_mul_right] at h2
      have h2p: p^m2 ∣ p^i := by
        have: p^m2 ∣ p^i * q^j := by
          apply Dvd.dvd.trans ?_ h2
          apply Nat.dvd_mul_right
        rwa [Nat.Coprime.dvd_mul_right] at this
        exact Nat.coprime_pow_primes m2 j pp pq pneq
      have h2q: q^n2 ∣ q^j := by
        have: q^n2 ∣ p^i * q^j := by
          refine Dvd.dvd.trans ?_ h2
          apply Nat.dvd_mul_left
        rwa [Nat.Coprime.dvd_mul_left] at this
        exact Nat.coprime_pow_primes n2 i pq pp pneq.symm
      have h1p: p^m1 ∣ p^i := by
        have: p^m1 ∣ p^i * q^j := by
          apply Dvd.dvd.trans ?_ h1
          apply Nat.dvd_mul_right
        rwa [Nat.Coprime.dvd_mul_right] at this
        exact Nat.coprime_pow_primes m1 j pp pq pneq
      have h1q: q^n1 ∣ q^j := by
        have: q^n1 ∣ p^i * q^j := by
          refine Dvd.dvd.trans ?_ h1
          apply Nat.dvd_mul_left
        rwa [Nat.Coprime.dvd_mul_left] at this
        exact Nat.coprime_pow_primes n1 i pq pp pneq.symm
      rw [pow_dvd_pow_iff pp.ne_zero (by simp [pp.ne_one])] at h1p h2p
      rw [pow_dvd_pow_iff pq.ne_zero (by simp [pq.ne_one])] at h1q h2q
      have hi: max m1 m2 ≤ i := max_le h1p h2p
      have hj: max n1 n2 ≤ j := max_le h1q h2q
      suffices p^(max m1 m2) * q^(max n1 n2) ∣ p^i * q^j by
        rw [ceq, deq, ← mul_assoc]
        exact Dvd.dvd.mul_right this e
      refine Nat.mul_dvd_mul ?_ ?_
      · exact Nat.pow_dvd_pow p hi
      · exact Nat.pow_dvd_pow q hj


/- Let $k$ be an integer strictly greater than 1.
If $m$ is a 3-digit positive integer such that $\mathop{\text{lcm}}[2^k \cdot m, 10^{10}] = 2^{k-1} \cdot \mathop{\text{lcm}}[m, 10^{10}]$,
show that $m=512$. -/
theorem number_theory_639516 (k m : ℕ) (hk : 1 < k) (hm: (Nat.digits 10 m).length = 3)
  (h : Nat.lcm (2 ^ k * m) (10 ^ 10) = 2 ^ (k - 1) * Nat.lcm m (10 ^ 10)) :
  m = 512 := by

  -- m is a 3-digit number, so 100 ≤ m < 1000
  have mnz: m ≠ 0 := by
    by_contra!
    simp [this] at hm
  have mge: m ≥ 100 := by
    have := Nat.base_pow_length_digits_le 10 m (by norm_num) mnz
    rw [hm] at this
    omega
  have mlt: m < 1000 := by
    rw [show 1000 = 10^3 by norm_num, ← hm]
    exact Nat.lt_base_pow_length_digits'

  -- let m = 2^a 5^b x, x does not contain factor 2,5.
  obtain ⟨a, b, x, meq, h2x, h5x⟩: ∃ (a b x: ℕ), m = 2^a * 5^b * x ∧
    ¬ 2 ∣ x ∧ ¬ 5 ∣ x := by
    have h2: 2 ≠ 1 := by norm_num
    have h3: 5 ≠ 1 := by norm_num
    have h4 := Nat.exists_eq_pow_mul_and_not_dvd mnz 2 h2
    rcases h4 with ⟨a, y, h4, ham⟩
    have h5: y ≠ 0 := by
      rw [ham] at mnz
      exact Nat.ne_zero_of_mul_ne_zero_right mnz
    replace h5 := Nat.exists_eq_pow_mul_and_not_dvd h5 5 h3
    rcases h5 with ⟨b, x, h5, hby⟩
    use a,b,x
    split_ands
    · rw [ham, hby, mul_assoc]
    · rw [hby] at h4
      contrapose! h4
      exact Dvd.dvd.mul_left h4 (5 ^ b)
    · exact h5

  -- x does not contain factor 2,5, therefore coprime to 10.
  have xco: Nat.Coprime x (10^10) := by
    have: 10^10 = 2^10 * 5^10 := by
      nth_rw 1 [show 10 = 2*5 by norm_num, Nat.mul_pow]
    rw [this, Nat.coprime_comm]
    refine Nat.Coprime.mul ?_ ?_
    all_goals
      rw [Nat.coprime_comm]
      apply Nat.Prime.coprime_pow_of_not_dvd
        (by norm_num) (by assumption)
  have xnz: x ≠ 0 := by
    by_contra!
    simp [meq, this] at mnz

  -- then lcm of 2^k m 10^10 is given
  have hleft: (2^k * m).lcm (10^10) =
    2^(max (k+a) 10) * (5^(max b 10) * x) := by
    have h1: 10^10 = 2^10 * 5^10 := by
      nth_rw 1 [show 10 = 2*5 by norm_num, Nat.mul_pow]
    have h2: (2^k * m).lcm (10^10) =
      (2^k * 2^a * 5^b).lcm (10^10) * x := by
      rw [meq, ← mul_assoc, ← mul_assoc]
      exact l_lcm_eq_lcm_mul_of_coprime xco
    have h3: (2^k * 2^a * 5^b).lcm (10^10) =
      2^(max (k+a) 10) * 5^(max b 10) := by
      rw [← pow_add, h1]
      apply l_lcm_prime_pow_mul
      <;> norm_num
    rw [h2, h3, mul_assoc]

  -- and lcm (m,10) is 2^(max a 10) 5^(max b 10) x
  have hright': m.lcm (10^10) =
    2^(max a 10) * 5^(max b 10) * x := by
    have: 10^10 = 2^10 * 5^10 := by
      nth_rw 1 [show 10 = 2*5 by norm_num, Nat.mul_pow]
    rw [meq, l_lcm_eq_lcm_mul_of_coprime xco, this]
    rw [l_lcm_prime_pow_mul]
    <;> norm_num
  have hright: 2^(k-1) * m.lcm (10^10) =
    2^(k-1 + (max a 10)) * (5^(max b 10) * x) := by
    rw [hright', ← mul_assoc, ← mul_assoc,
    ← pow_add, mul_assoc]

  -- by problem statement, we obtain max (k+a, 10) = k-1 + max(a,10)
  replace h: max (k+a) 10 = k-1 + max a 10 := by
    rw [hleft, hright] at h
    have: 5^(max b 10) * x ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
      Nat.max_eq_zero_iff, and_false, not_false_eq_true, and_true, xnz, or_self]
    simp only [mul_eq_mul_right_iff, Nat.ofNat_pos, ne_eq,
    OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀, this, or_false] at h
    exact h

  -- then a < 10
  have alt: a < 10 := by
    by_contra! h1
    have h2: max (k+a) 10 = k+a := by
      refine Nat.max_eq_left ?_
      linarith only [h1]
    simp only [h2, h1, sup_of_le_left, Nat.add_right_cancel_iff] at h
    absurd h
    clear * - hk
    omega

  -- then we solve a = 9
  have aeq: a = 9 := by
    rw [sup_of_le_right alt.le] at h
    have h1: k+a > 10 := by
      by_contra!
      rw [sup_of_le_right this] at h
      clear * - hk h
      omega
    rw [sup_of_le_left h1.le] at h
    omega

  replace meq: m = 512 * (5^b * x) := by
    rw [meq, mul_assoc]
    simp [aeq]

  -- m = 512 multiply some, and it's a three-digit number, then it can only be 512.
  suffices (5^b * x) < 2 by
    have h1: 5^b * x ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
      false_and, xnz, or_self, not_false_eq_true]
    have h2: 5^b * x = 1 := by omega
    rw [meq, h2, mul_one]

  have: 512 * (5^b*x) < 512 * 2 := by
    rw [← meq]
    apply mlt.trans (by norm_num)
  exact Nat.lt_of_mul_lt_mul_left this