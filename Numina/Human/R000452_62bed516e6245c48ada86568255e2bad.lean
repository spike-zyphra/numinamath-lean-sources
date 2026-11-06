import Mathlib

/-Both roots of the quadratic equation $x^2 - 63 x + k = 0$ are prime numbers. How many possible values of $k$ are there?-/
theorem algebra_10708 :
    {k | ∃ p q : ℕ, p ≠ q ∧ p^2 - 63 * p + k = (0 : ℝ) ∧ q^2 - 63 * q + k = (0 : ℝ) ∧ p.Prime ∧ q.Prime }.ncard = 1 := by
  -- Let $p$ and $q$ be two primes that are roots of $x^2 - 63 x + k = 0$. Then $$
  --x^2 - 63 x + k = (x - p)(x - q) = x^2 - (p+q)x + p \cdot q,
  --$$ so $p + q = 63$ and $p\cdot q=k$. Since $63$ is odd, one of the primes must be $2$ and the other $61$. Thus, there is exactly $\boxed{1}$ possible value for $k$, namely $k = p\cdot q = 2\cdot 61=122$.
  have : {k | ∃ p q : ℕ, p ≠ q ∧ p^2 - 63 * p + k = (0 : ℝ) ∧ q^2 - 63 * q + k = (0 : ℝ) ∧ p.Prime ∧ q.Prime } = {122} := by
    ext k
    simp
    constructor
    · intro ⟨p, q, hpq, hpp, hqq, hp, hq⟩
      have : |(2 * 1 * p + -63 : ℝ)| = |(2 * 1 * q + -63 : ℝ)| := by
        rw [←one_mul (q ^ 2 : ℝ)] at hqq
        rw [←one_mul (p ^ 2 : ℝ)] at hpp
        rw [pow_two, sub_eq_add_neg, ←neg_mul, ←mul_assoc] at hpp hqq
        rw [mul_assoc, quadratic_eq_zero_iff_discrim_eq_sq (by norm_num)] at hpp hqq
        apply (sq_eq_sq_iff_abs_eq_abs _ _).mp
        rw [hpp.symm, hqq]
      rw [abs_eq_abs] at this
      obtain (r | r) := this
      . --  2 * 1 * ↑p + -63 = 2 * 1 * ↑q + -63
        have : (p : ℝ) = (q : ℝ) := by linarith
        absurd this
        norm_cast

      have sum_pq: p + q = (63 : ℝ) := by linarith
      have prod_pq: p * q = (k : ℝ) := by
        rw [sum_pq.symm] at hpp
        linarith
      norm_cast at sum_pq prod_pq
      rw [prod_pq.symm]
      obtain (even_p | odd_p) := Nat.even_or_odd p
      . -- Even p
        have : p = 2 := by exact (Nat.Prime.even_iff hp).mp even_p
        rw [this] at sum_pq
        rw [this]
        norm_cast
        linarith
      . -- Odd p
        have : Even q := by
          have : q = 63 - p := by exact Nat.eq_sub_of_add_eq' sum_pq
          rw [this]
          exact Nat.Odd.sub_odd (Nat.odd_iff.mpr rfl) odd_p
        have : q = 2 := by exact (Nat.Prime.even_iff hq).mp this
        rw [this] at sum_pq
        rw [this]
        norm_cast
        linarith
    · intro hk
      rw [hk]
      use 2
      use 61
      norm_num
  rw [this]
  simp
