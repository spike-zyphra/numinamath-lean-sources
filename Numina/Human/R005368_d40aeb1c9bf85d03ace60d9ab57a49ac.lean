import Mathlib


/- Consider a non-constant arithmetic progression $a_{1}, a_{2}, \ldots, a_{n}, \ldots$ 
Suppose there exist relatively prime positive integers $p>1$ and $q>1$ such that $a_{1}^{2}, a_{p+1}^{2}$ and $a_{q+1}^{2}$ are also the terms of the same arithmetic progression. 
Prove that the terms of the arithmetic progression are all integers. -/
theorem number_theory_607913 (a : ℕ → ℝ) {d:ℝ} (hd: d ≠ 0)
  (h : ∀ n, n ≥ 1 → a n = a 1 + d * (n-1))
  (h' : ∃ p q : ℕ, p > 1 ∧ q > 1 ∧ Nat.Coprime p q ∧
      ∃ (k l m: ℕ), k ≥ 1 ∧ l ≥ 1 ∧ m ≥ 1 ∧  a 1 ^ 2 = a k ∧ a (p + 1) ^ 2 = a l ∧ a (q + 1) ^ 2 = a m) :
    ∀ n, n ≥ 1 → ∃ m : ℤ, a n = m := by

  -- by problem statement, a1^2, a_{p+1}^2, a_{q+1}^2 are also terms of the sequence.
  -- suppose they are a_k, a_l, a_m.
  rcases h' with ⟨p, q, pgt, qgt, co_pq, h'⟩
  rcases h' with ⟨k', l', m', k'ge, l'ge, m'ge, hak', hal', ham'⟩

  -- denote a1 = aa, simplify these equations
  set aa: ℝ := a 1 with aa_def
  obtain ⟨k, hak⟩: ∃ (k:ℕ), aa^2 = aa + k*d := by
    rw [hak', h k' k'ge]
    use (k'-1)
    rw [Nat.cast_sub k'ge]
    ring
  obtain ⟨l, hal⟩: ∃ (l:ℕ), (aa + p*d)^2 = aa + l*d := by
    have := h (p+1) (by simp)
    rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    mul_comm d p] at this
    rw [← this, hal', h l' l'ge]
    use (l'-1)
    rw [Nat.cast_sub l'ge]
    ring
  obtain ⟨m, ham⟩: ∃ (m:ℕ), (aa + q*d)^2 = aa + m*d := by
    have := h (q+1) (by simp)
    rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    mul_comm d q] at this
    rw [← this, ham', h m' m'ge]
    use (m'-1)
    rw [Nat.cast_sub m'ge]
    ring

  -- combine hak and hal, we have 2pa + p^2d = l-k
  have hlk: 2*p*aa + p^2*d = l - k := by
    have: (aa+p*d)^2 = aa^2 + 2*aa*p*d + p^2*d^2 := by ring
    rw [this, hak] at hal
    replace hal: d*(2*p*aa+ p^2*d) = d * (l-k) := by
      linarith only [hal]
    simp only [mul_eq_mul_left_iff, hd, or_false] at hal
    exact hal

  -- similarly, we have 2qa + q^2d = m-k
  have hmk: 2*q*aa + q^2*d = m - k := by
    have: (aa+q*d)^2 = aa^2 + 2*aa*q*d + q^2*d^2 := by ring
    rw [this, hak] at ham
    replace ham: d*(2*q*aa+q^2*d) = d*(m-k) := by
      linarith only [ham]
    simp only [mul_eq_mul_left_iff, hd, or_false] at ham
    exact ham

  -- p^2q - pq^2 ≠ 0, otherwise p = q
  have: (p^2*q:ℤ) - p*q^2 ≠ 0 := by
    have: (p^2*q:ℤ) - p*q^2 = (p*q)*(p-q) := by ring
    rw [this]
    have hp: p ≠ 0 := Nat.not_eq_zero_of_lt pgt
    have hq: q ≠ 0 := Nat.not_eq_zero_of_lt qgt
    replace: (p-q:ℤ) ≠ 0 := by
      rintro heq
      replace heq: p = q := by
        zify
        exact Int.eq_of_sub_eq_zero heq
      simp only [heq, Nat.coprime_self] at co_pq
      simp [co_pq] at qgt
    simp [hp, hq, this]
  rify at this

  -- from these two equations, we can write aa and d in terms of p,q.
  have aa_pq: aa = (p^2*(m-k) - q^2*(l-k)) / (2 * (p^2*q-p*q^2)) := by
    field_simp only [this]
    rw [← hlk, ← hmk]
    ring
  have d_pq: d = (q*(l-k) - p*(m-k)) / (p^2*q - p*q^2) := by
    field_simp only [this]
    rw [← hlk, ← hmk]
    ring

  -- also, notice that p^2aa^2 = (p-2k) p aa + k (l-k)
  have heq: p^2 * aa^2 + (-(p-2*k)*p)*aa + (-k*(l-k)) = 0 := by
    have h1: p^2*aa^2 = p^2*aa + k*(p^2*d) := by
      rw [hak]
      ring
    have h2: p^2*d = l - k - 2*p*aa := by linarith only [hlk]
    rw [h1, h2]
    ring
  replace heq: (p*aa)^2 + (-(p-2*k)) * (p*aa) + (-k*(l-k)) = 0 := by
    linarith only [heq]
  -- thus p aa is a solution to the quadratic equation.
  -- and by expressing aa in terms of p,q,m,k, we show aa is rational.
  have rat_aa: ∃ (aa':ℚ), aa = aa' := by
    use ((p^2*(m-k) - q^2*(l-k)) / (2 * (p^2*q-p*q^2)))
    rw [aa_pq]
    norm_cast
  rcases rat_aa with ⟨aa', haa'⟩
  have rat_d: ∃ (d':ℚ), d = d' := by
    use (q*(l-k) - p*(m-k)) / (p^2*q - p*q^2)
    rw [d_pq]
    norm_cast
  rcases rat_d with ⟨d', hd'⟩


  -- and we argue if a monic quadratic equation with integer coefficients have rational solution,
  -- then that rational solution is integer.
  have int_of_monic_quadratic {x:ℚ} {b c: ℤ}
    (hh: x^2 + b*x + c = 0):
    ∃ x':ℤ, x' = x := by
    suffices IsLocalization.IsInteger ℤ x by
      dsimp [IsLocalization.IsInteger] at this
      simpa only [RingHom.mem_rangeS, eq_intCast] using this
    set P: Polynomial ℤ := 1 * Polynomial.X^2 +
      Polynomial.C b * Polynomial.X + Polynomial.C c with P_def
    have h1: Polynomial.Monic P := by
      have: P.natDegree = 2 := by
        apply Polynomial.natDegree_quadratic (by norm_num)
      rw [Polynomial.Monic.def, Polynomial.leadingCoeff, this, P_def]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_mul_X]
      simp
    have h2: P.aeval x = 0 := by
      simp [P_def, hh]
    exact isInteger_of_is_root_of_monic h1 h2

  -- so pa is integer
  have int_pa: ∃ i:ℤ, i = p*aa' := by
    rw [haa'] at heq
    norm_cast at heq
    apply int_of_monic_quadratic heq

  -- similarly, we can show qa is also integer.
  replace heq: q^2 * aa^2 -(q-2*k)*q*aa - k*(m-k) = 0 := by
    have h1: q^2 * aa^2 = q^2 * aa + k*(q^2*d) := by
      rw [hak]
      ring
    have h2: q^2*d = m - k - 2*q*aa := by linarith only [hmk]
    rw [h1, h2]
    ring
  replace heq: (q*aa)^2 + (-(q-2*k)) * (q*aa) + (-k*(m-k)) = 0 := by
    linarith only [heq]
  rw [haa'] at heq
  norm_cast at heq
  have int_qa: ∃ i:ℤ, i = q*aa' := by
    apply int_of_monic_quadratic heq

  -- since p,q coprime, exist u,v, pu + qv = 1
  rcases (exists_gcd_eq_mul_add_mul (p:ℤ) q) with ⟨u, v, huv⟩
  replace: gcd (p:ℤ) q = 1 := by
    rw [← Nat.isCoprime_iff_coprime,
    Int.isCoprime_iff_gcd_eq_one] at co_pq
    have: (1:ℤ) = ↑(1:ℕ) := by simp
    rw [this, ← co_pq]
    norm_cast
  rw [this] at huv
  -- mutiply a to both sides, we show a is integer.
  replace huv: (1:ℤ) * aa' = (p*aa') * u + (q*aa') * v := by
    rw [huv]
    push_cast
    ring
  simp only [Int.cast_one, one_mul] at huv
  have a_int: ∃ (ai: ℤ), ai = aa := by
    rw [haa']
    rcases int_pa with ⟨i1, hi1⟩
    rcases int_qa with ⟨i2, hi2⟩
    use (i1*u + i2*v)
    rw [huv, ← hi1, ← hi2]
    norm_cast

  -- thus p^2d, q^2d is integer. but p^2, q^2 coprime,
  -- denominator of d can only be 1.
  -- otherwise it's a common divisor of p^2,q^2.
  have d_int: d'.num = d := by
    rw [hd']
    norm_cast
    refine Rat.coe_int_num_of_den_eq_one ?_
    have h1: (p^2).Coprime (q^2) := by
      exact Nat.Coprime.pow 2 2 co_pq
    have h2: p^2 * d = l-k-2*p*aa := by
      linarith only [hlk]
    rw [hd'] at h2
    replace h2: (d'.den:ℤ) ∣ p^2 * d'.num := by
      rcases int_pa with ⟨i1, hi1⟩
      rw [haa', mul_assoc] at h2
      norm_cast at h2
      rw [← hi1] at h2
      use (l-k-2*i1)
      qify
      rw [← Rat.mul_den_eq_num, ← mul_assoc]
      push_cast at h2
      rw [h2]
      ring
    replace h2: d'.den ∣ p^2 * d'.num.natAbs := by
      zify
      rw [← dvd_abs, abs_mul] at h2
      nth_rw 1 [abs_of_nonneg (sq_nonneg _)] at h2
      exact h2
    have h3: q^2 * d = m - k - 2*q*aa := by
      linarith only [hmk]
    replace h3: (d'.den: ℤ) ∣ q^2 * d'.num := by
      rcases int_qa with ⟨i2, hi2⟩
      rw [haa', hd', mul_assoc] at h3
      norm_cast at h3
      rw [← hi2] at h3
      use (m-k-2*i2)
      qify
      push_cast at h3
      rw [← Rat.mul_den_eq_num, ← mul_assoc, h3]
      ring
    replace h3: d'.den ∣ q^2 * d'.num.natAbs := by
      zify
      rw [← dvd_abs, abs_mul] at h3
      nth_rw 1 [abs_of_nonneg (sq_nonneg _)] at h3
      exact h3
    have: Nat.Coprime d'.den d'.num.natAbs := by
      refine Nat.coprime_comm.mp ?_
      exact d'.reduced
    rw [Nat.Coprime.dvd_mul_right this] at h2 h3
    have h4: d'.den ∣ Nat.gcd (p^2) (q^2) := Nat.dvd_gcd h2 h3
    rw [h1] at h4
    rwa [Nat.dvd_one] at h4

  -- since a and d are both integers, the arithmetic sequence is all integer.
  intro n hn
  rcases a_int with ⟨ai, hai⟩
  rw [h n hn, ← hai, ← d_int]
  use (ai + d'.num * (n-1))
  push_cast
  ring