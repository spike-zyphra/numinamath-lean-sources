import Mathlib

/- For polynomial $P(x) = 1 - \frac{1}{3}x + \frac{1}{6}x^2$, define
$Q(x) = P(x)P(x^3)P(x^5)P(x^7)P(x^9) = \sum_{i=0}^{50} a_i x^i$. Then
$\sum_{i=0}^{50} |a_i| = \frac{m}{n}$, where $m$ and $n$ are relatively
prime positive integers. Find $m + n$. -/
theorem algebra_96893 {P : Polynomial ℝ} (hP : P = Polynomial.C 1 - Polynomial.C (1 / 3) * Polynomial.X + Polynomial.C (1 / 6) * Polynomial.X ^ 2)
    (Q : Polynomial ℝ) (hQ : Q = P * P.comp (Polynomial.X ^ 3) * P.comp (Polynomial.X ^ 5) * P.comp (Polynomial.X ^ 7) * P.comp (Polynomial.X ^ 9))
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) (hsum : ∑ i ∈ Finset.range 51, |Q.coeff i| = m / n) : m + n = 275 := by

  -- We note that $P$ has coefficients that alternate between positive and negative,
  -- and that this pattern is preserved when we multiply two such polynomials, or
  -- compose them with a odd power of $x$. Let's call such polynomials "alternating".
  let Alternating (p : Polynomial ℝ) := ∀ i : ℕ, |p.coeff i| = p.coeff i * (-1) ^ i

  -- The key property is that for an alternating polynomial, summing the absolute values
  -- of its coefficients is the same as evaluating it at $-1$.
  have alternating_sum_abs {p : Polynomial ℝ} {n : ℕ} (hp : Alternating p) (hn : p.natDegree < n) :
      ∑ i ∈ Finset.range n, |p.coeff i| = p.eval (-1) := by
    calc
      ∑ i ∈ Finset.range n, |p.coeff i| = ∑ i ∈ Finset.range n, p.coeff i * (-1) ^ i := Finset.sum_congr rfl (fun i _ => hp i)
      _ = p.eval (-1) := by rw [Polynomial.eval_eq_sum_range' hn (-1)]

  -- The product of two alternating polynomials is alternating, by expanding each coefficient
  -- as a sum of products of input coefficients.
  have alternating_mul {p q : Polynomial ℝ} (hp : Alternating p) (hq : Alternating q) : Alternating (p * q) := by
    intro i
    have c_le := calc
      |(p * q).coeff i| = |∑ x ∈ Finset.antidiagonal i, p.coeff x.1 * q.coeff x.2| := by rw [Polynomial.coeff_mul]
      _ ≤ ∑ x ∈ Finset.antidiagonal i, |p.coeff x.1 * q.coeff x.2| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ Finset.antidiagonal i, |p.coeff x.1| * |q.coeff x.2| := by simp [abs_mul]
      _ = ∑ x ∈ Finset.antidiagonal i, (p.coeff x.1 * q.coeff x.2) * (-1) ^ (x.1 + x.2) := Finset.sum_congr rfl (fun x _ => by rw [hp, hq]; ring_nf)
      _ = ∑ x ∈ Finset.antidiagonal i, (p.coeff x.1 * q.coeff x.2) * (-1) ^ i := Finset.sum_congr rfl (fun x h => by rw [Finset.mem_antidiagonal] at h; rw [h])
      _ = (∑ x ∈ Finset.antidiagonal i, p.coeff x.1 * q.coeff x.2) * (-1) ^ i := by rw [Finset.sum_mul]
      _ = (p * q).coeff i * (-1) ^ i := by rw [Polynomial.coeff_mul]
    cases Nat.even_or_odd i with
    | inl h_even =>
      simp [h_even];
      simp [h_even] at c_le;
      cases abs_cases ((p * q).coeff i) <;> linarith
    | inr h_odd =>
      simp [h_odd];
      simp [h_odd] at c_le;
      cases abs_cases ((p * q).coeff i) <;> linarith

  -- Composition with an odd power of $x$ preserves the alternating property.
  have alternating_comp {p : Polynomial ℝ} {n : ℕ} (hp : Alternating p) (hn : Odd n) : Alternating (p.comp (Polynomial.monomial n 1)) := by
    have hnz : n ≠ 0 := by
      intro h
      rw [h] at hn
      exact Nat.not_odd_zero hn
    intro i
    simp [Polynomial.comp, Polynomial.eval₂_def, Polynomial.sum_over_range, Polynomial.coeff_monomial]
    by_cases h : n ∣ i
    . obtain ⟨k, hk⟩ := h
      match Nat.decLt k (p.natDegree + 1) with
      | isTrue h' =>
        simp [hk, hn, hnz, h', pow_mul]
        exact hp k
      | isFalse h' =>
        simp [hk, hnz, h']
    . have (j : ℕ) : n * j ≠ i := fun h' => h (Dvd.intro j h')
      rw [Finset.sum_ite_of_false (fun j _ => this j) _ _]
      simp

  -- $P$ is alternating by inspection.
  have P_alternating : Alternating P := by
    intro n
    simp only [hP, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
    match n with
    | 0 => simp
    | 1 => simp
    | 2 => simp
    | (n + 3) => simp

  -- Therefore, $Q$ is alternating by repeatedly applying the properties above.
  have Q_alternating : Alternating Q := by
    rw [hQ]
    simp only [Polynomial.X_pow_eq_monomial]
    repeat refine alternating_mul ?_ ?_
    any_goals refine alternating_comp ?_ (by decide)
    all_goals exact P_alternating

  -- We verify that $Q$ has degree at most 50 based on its structure.
  have Q_degree : Q.natDegree ≤ 50 := by
    simp [hQ]
    have P_degree : P.natDegree ≤ 2 := by simp [hP]; compute_degree!
    have P_comp_degree (n : ℕ) : (P.comp (Polynomial.X ^ n)).natDegree ≤ 2 * n := by
      rw [Polynomial.X_pow_eq_monomial]
      calc
        (P.comp (Polynomial.monomial n 1)).natDegree ≤ P.natDegree * (Polynomial.monomial n 1).natDegree := Polynomial.natDegree_comp_le
        _ ≤ 2 * n := Nat.mul_le_mul P_degree (Polynomial.natDegree_monomial_le 1)
    have :=
      (Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_mul_le_of_le
          (Polynomial.natDegree_mul_le_of_le
            (Polynomial.natDegree_mul_le_of_le
              P_degree
              (P_comp_degree 3))
            (P_comp_degree 5))
          (P_comp_degree 7))
        (P_comp_degree 9))
    norm_num at this
    exact this

  -- Now we can compute our sum as $Q(-1) = P(-1)^5$.
  have : ∑ i ∈ Finset.range 51, |Q.coeff i| = 243 / 32 := by
    rw [alternating_sum_abs Q_alternating (Nat.lt_succ_of_le Q_degree)]
    simp [hQ, hP]
    norm_num

  -- All that's left is to compute $m + n$.
  rw [this] at hsum
  obtain ⟨_, _⟩ := @Rat.div_int_inj m n 243 32 (by simpa) (by norm_num) (by simpa) (by norm_num) (by rify; linarith)
  linarith