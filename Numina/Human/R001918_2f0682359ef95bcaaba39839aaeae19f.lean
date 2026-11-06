import Mathlib

/- for natural numbers a,b, extract their greatest common factor, the remaining are coprime.-/
lemma exists_coprime_mul_gcd_nat {a: ℕ} (ha: 0 < a) (b: ℕ) :
  ∃ t r s, a = t * r ∧ b = t * s ∧ Nat.Coprime r s ∧ 0 < t := by
  use (a.gcd b),  (a / (a.gcd b)), (b / (a.gcd b))
  have h1: a.gcd b ∣ a := Nat.gcd_dvd_left a b
  have h2: a.gcd b ∣ b := Nat.gcd_dvd_right a b
  have h3: 0 < a.gcd b := Nat.gcd_pos_of_pos_left b ha
  simp only [h1, Nat.mul_div_cancel', h2, h3, and_true, true_and]
  exact Nat.coprime_div_gcd_div_gcd h3

/- natural numbers r,s. if r,s are coprime, then rs and r+s are coprime  -/
lemma mul_coprime_add {r s: ℕ} (co: Nat.Coprime r s):
  Nat.Coprime (r*s) (r+s) := by
  refine Nat.Coprime.mul ?_ ?_
  · exact Nat.coprime_self_add_right.mpr co
  · exact Nat.coprime_add_self_right.mpr co.symm

/- 2017 x 2 is not squarefree  -/
lemma sqfree_2017_mul_2: Squarefree (2017 * 2) := by
  rw [Nat.squarefree_mul_iff]
  refine ⟨(by norm_num), ?_, ?_⟩
  · apply Prime.squarefree
    refine Nat.Prime.prime (by norm_num)
  · exact Nat.squarefree_two

/- 2018 is not square free -/
lemma sqfree_2018: Squarefree 2018 := by
  have: 2018 = 2 * 1009 := by norm_num
  rw [this, Nat.squarefree_mul_iff]
  refine ⟨(by norm_num), ?_, ?_⟩
  · exact Nat.squarefree_two
  · apply Prime.squarefree
    refine Nat.Prime.prime (by norm_num)

/- if n ≠ 1 is squarefree, then n is not a perfect square. -/
lemma sq_ne_of_sqfree {t n: ℕ} (n_not_1: n ≠ 1) (h: Squarefree n):
  t^2 ≠ n := by
  by_contra!
  have hh: t^2 ∣ n := dvd_of_eq this
  rw [pow_two] at hh
  dsimp only [Squarefree] at h
  specialize h t hh
  simp only [Nat.isUnit_iff] at h
  simp [← this, h] at n_not_1

/- Show that the equation
 $$a^2b=2017(a+b)$$
 has no solutions for positive integers $a$ and $b$.

[i]Proposed by Oriol Solé[/i] -/
theorem number_theory_45210 : ¬∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a^2 * b = 2017 * (a + b) := by
  -- suppose on the contrary, exists such a,b.
  rintro ⟨a, b, apos, bpos, heq⟩
  -- suppose a = tr, b = ts, r and s are coprime
  rcases (exists_coprime_mul_gcd_nat apos b) with
    ⟨t, r, s, ha, hb, co_rs, tpos⟩

  -- subsitute values in, simplify.
  replace heq: t^2 * (r^2 * s) = 2017 * (r+s) := by
    have h1: (t*r)^2 * (t*s) = t^2 * (r^2 * s) * t := by ring
    have h2: 2017 * (t*r + t*s) = 2017 * (r+s) * t := by ring
    rw [ha, hb, h1, h2] at heq
    exact Nat.eq_of_mul_eq_mul_right tpos heq

  -- r^2s and (r+s) are coprime, so r^2s divide 2017
  have hdvd: r^2*s ∣ 2017 := by
    have h1: r^2 * s ∣ 2017 * (r+s) := by
      rw [← heq]
      apply Nat.dvd_mul_left
    have h2: Nat.Coprime (r^2 * s) (r + s) := by
      rw [pow_two, mul_assoc r r s]
      refine Nat.Coprime.mul ?_ ?_
      · exact Nat.coprime_self_add_right.mpr co_rs
      · exact mul_coprime_add co_rs
    exact Nat.Coprime.dvd_of_dvd_mul_right h2 h1

  -- r = 1, since 2017 is prime, certainly cannot contain square > 1.
  have p2017: Nat.Prime 2017 := by norm_num
  have req: r = 1 := by
    have: r ∣ 2017 := by
      apply Dvd.dvd.trans ?_ hdvd
      rw [pow_two, mul_assoc r r s]
      apply Nat.dvd_mul_right
    rw [Nat.dvd_prime p2017] at this
    rcases this with r1 | r2017
    · exact r1
    · have: r^2 ∣ 2017 := by
        apply Dvd.dvd.trans ?_ hdvd
        apply Nat.dvd_mul_right
      norm_num [r2017] at this

  -- 2017 is prime, s divide 2017, s = 1 or 2017
  rw [req, one_pow, one_mul, Nat.dvd_prime p2017] at hdvd
  rcases hdvd with seq | seq
  · -- s=1 case.
    -- r=1, s=1, then t^2 = 2017 x 2.
    simp only [req, one_pow, seq, mul_one,
    Nat.reduceAdd] at heq
    absurd heq
    apply sq_ne_of_sqfree (by norm_num) ?_
    apply sqfree_2017_mul_2
  · -- s= 2017 case.
    simp only [req, one_pow, seq, one_mul,
    Nat.reduceAdd, mul_comm 2017 2018] at heq
    rw [mul_eq_mul_right_iff] at heq
    simp only [OfNat.ofNat_ne_zero, or_false] at heq
    absurd heq
    apply sq_ne_of_sqfree (by norm_num) ?_
    apply sqfree_2018