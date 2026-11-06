import Mathlib

open Polynomial Finset

-- If all coefficients of p are positive then p ≠ 0.
lemma ne_zero_of_pos_coeffs {p : ℝ[X]} (hp : ∀ i ≤ p.natDegree, 0 < p.coeff i) : p ≠ 0 := by
  -- It is enough to show that the leading coefficient of p is not zero.
  rw [← leadingCoeff_ne_zero, leadingCoeff]
  apply ne_of_gt (hp _ (le_refl _))

-- If all coefficients of p are positive then 0 ≤ p.coeff i for all i.
lemma nonneg_coeffs_of_pos_coeffs {p : ℝ[X]} (hp : ∀ i ≤ p.natDegree, 0 < p.coeff i) :
    ∀ i, 0 ≤ p.coeff i := by
  intro i
  by_cases hi : i ≤ p.natDegree
  · -- If i ≤ p.natDegree then 0 < p.coeff i.
    apply le_of_lt (hp i hi)
  · -- If p.natDegree < i then p.coeff i = 0 ≥ 0.
    simp at hi
    rw [coeff_eq_zero_of_natDegree_lt hi]

-- If all coefficients of p and q are positive then all coefficients of p + q are positive.
lemma pos_coeffs_add {p q : ℝ[X]} (hp : ∀ i ≤ p.natDegree, 0 < p.coeff i) (hq : ∀ i ≤ q.natDegree, 0 < q.coeff i) :
    ∀ i ≤ (p + q).natDegree, 0 < (p + q).coeff i := by
  -- Without loss of generality, assume that p.natDegree ≤ q.natDegree.
  wlog hpq : p.natDegree ≤ q.natDegree
  · -- If p.natDegree > q.natDegree then swap p and q.
    rw [add_comm]
    apply this hq hp (by linarith)
  intro i hi
  rw [coeff_add]
  -- Show that 0 < p.coeff i + q.coeff i for i ≤ (p + q).natDegree ≤ q.natDegree.
  have h := natDegree_add_le p q
  rw [Nat.max_eq_right hpq] at h
  -- We have 0 < q.coeff i and 0 ≤ p.coeff i, so 0 < p.coeff i + q.coeff i.
  have hqi := hq i (by linarith)
  linarith [nonneg_coeffs_of_pos_coeffs hp i]

-- If all coefficients of p and q are positive then all coefficients of p * q are positive.
lemma pos_coeffs_mul {p q : ℝ[X]} (hp : ∀ i ≤ p.natDegree, 0 < p.coeff i) (hq : ∀ i ≤ q.natDegree, 0 < q.coeff i) :
    ∀ i ≤ (p * q).natDegree, 0 < (p * q).coeff i := by
  -- The degree of p * q is p.natDegree + q.natDegree (because p ≠ 0 and q ≠ 0).
  rw [natDegree_mul (ne_zero_of_pos_coeffs hp) (ne_zero_of_pos_coeffs hq)]
  intro i hi
  -- The i-th coefficient of p * q is ∑ (a + b = i), p.coeff a * q.coeff b.
  rw [coeff_mul]
  apply sum_pos'
  · -- Show that 0 ≤ p.coeff a * q.coeff b for all a and b.
    intro i hi
    -- The result follows from 0 ≤ p.coeff a and 0 ≤ q.coeff b for all a and b.
    apply mul_nonneg (nonneg_coeffs_of_pos_coeffs hp i.1) (nonneg_coeffs_of_pos_coeffs hq i.2)
  · -- Show that 0 < p.coeff a * q.coeff b for some a and b such that a + b = i.
    simp only [mem_antidiagonal, Prod.exists]
    -- Take a = min i p.natDegree and b = i - min i p.natDegree.
    use min i p.natDegree, i - min i p.natDegree
    simp
    apply mul_pos
    · -- We have a ≤ p.natDegree, so 0 < p.coeff a.
      apply hp
      simp only [inf_le_right]
    · -- Show that b ≤ q.natDegree:
      -- b = i - min i p.natDegree ≤ q.natDegree.
      apply hq
      omega

-- If all coefficients of p are positive then all coefficients of p^n are positive.
lemma pos_coeffs_pow {p : ℝ[X]} {n : ℕ} (hp : ∀ i ≤ p.natDegree, 0 < p.coeff i) :
    ∀ i ≤ (p ^ n).natDegree, 0 < (p ^ n).coeff i := by
  -- Proof by induction
  induction n with
  -- p^0 = 1, so all coefficients of p^0 are positive.
  | zero => simp
  | succ n ih =>
    -- p^(n + 1) = p^n * p, p^n and p have positive coefficients, so all coefficients of
    -- p^n * p are positive.
    rw [pow_succ]
    apply pos_coeffs_mul ih hp

/- 10.8. Let $P(x)=a_{n} x^{n}+a_{n-1} x^{n-1}+\ldots+a_{0}$ be a polynomial with real coefficients, and $a_{n} \geqslant 1$. Prove that if the number $m$ is greater than any of the numbers $\left|a_{n-1}\right|+1, \ldots$ $\ldots,\left|a_{0}\right|+1$, then $Q(x)=P(x+m)$ is a polynomial with positive coefficients. -/
theorem algebra_225133 {P Q : ℝ[X]} (hP1 : 1 ≤ P.leadingCoeff)
    {m : ℝ} (hm : ∀ i < P.natDegree, m > |P.coeff i| + 1)
    (hQ : Q = P.comp (X + C m)) :
    ∀ i ≤ Q.natDegree, 0 < Q.coeff i := by
  -- Let n be the degree of P.
  generalize hn : P.natDegree = n
  -- Consider two cases: n = 0 or n ≠ 0.
  by_cases hn0 : n = 0
  · rw [hn0] at hn
    rw [natDegree_eq_zero] at hn
    -- If n = 0 then P = c for some c ∈ ℝ such that 1 ≤ c.
    have ⟨c, hc⟩ := hn
    subst P
    simp at hQ hP1
    subst Q
    -- We get Q = c and c > 0.
    simp
    linarith
  -- Assume now that n ≠ 0.
  -- Show that 1 < m.
  have hm1 : 1 < m := by
    -- n ≠ 0 implies that m > |P.coeff 0| + 1 ≥ 1.
    have := hm 0 (by omega)
    linarith [abs_nonneg (P.coeff 0)]
  -- Prove that P = C (P.coeff n - 1) * X^n + ∑ i ∈ range n, (X + C (P.coeff i - 1)) * X^i + C 1.
  have heq : P = C (P.coeff n - 1) * X^n + ∑ i ∈ range n, (X + C (P.coeff i - 1)) * X^i + C 1 := by
    -- It is enough to show that P(x) = (P.coeff n - 1) * x^n + ∑ i ∈ range n, (x + (P.coeff i - 1)) * x^i + 1
    -- for all x ∈ ℝ.
    apply Polynomial.funext
    intro x
    rw [eval_eq_sum_range, ← hn]
    simp [eval_finset_sum, add_mul, leadingCoeff, hn]
    symm
    calc
      -- We have
      -- ∑ i ∈ range n, (x + (P.coeff i - 1)) * x^i
      --     = ∑ i ∈ range n, (x^(i + 1) - x^i) + ∑ i ∈ range n, P.coeff i * x^i
      --     = x^n - x^0 + ∑ i ∈ range n, P.coeff i * x^i.
      _ = P.coeff n * x^n - x^n + ∑ i ∈ range n, (x^(i + 1) - x^i + P.coeff i * x^i) + 1 := by
        rw [sub_mul, one_mul]
        congr 2
        apply sum_congr rfl
        intro i hi
        ring
      -- P.coeff n * x^n - x^n + x^n - x^0 + ∑ i ∈ range n, P.coeff i * x^i + 1
      --    = ∑ i ∈ range (n + 1), P.coeff i * x^i = P(x).
      _ = P.coeff n * x^n - x^n + ((x^n - 1) + ∑ i ∈ range n, P.coeff i * x^i) + 1 := by
        rw [sum_add_distrib]
        congr
        rw [sum_range_sub, pow_zero]
      _ = ∑ i ∈ range (n + 1), P.coeff i * x^i := by
        rw [sum_range_succ]
        ring
  -- Show that
  -- Q = C (P.coeff n - 1) * (X + C m)^n + ∑ i ∈ range n, (X + C (m + P.coeff i - 1)) * (X + C m)^i + C 1.
  replace heq : Q = C (P.coeff n - 1) * (X + C m)^n + ∑ i ∈ range n, (X + C (m + P.coeff i - 1)) * (X + C m)^i + C 1 := by
    simp [hQ]
    nth_rw 1 [heq]
    simp
    apply sum_congr rfl
    intro i hi
    ring
  -- We have (X + C c).coeff 0 = c and (X + C c).coeff 1 = 1.
  have hc0 {c : ℝ} : (X + C c).coeff 0 = c := by simp
  have hc1 {c : ℝ} : (X + C c).coeff 1 = 1 := by simp
  -- Show that all coefficients of X + C (m + P.coeff j - 1) are positive for any j.
  have h1 j : ∀ i ≤ (X + C (m + P.coeff j - 1)).natDegree, 0 < (X + C (m + P.coeff j - 1)).coeff i := by
    -- The degree of any linear polynomial is 1.
    rw [natDegree_X_add_C]
    intro i hi
    interval_cases i
    · -- Consider (X + C (m + P.coeff j - 1)).coeff 0 = m + P.coeff j - 1.
      rw [hc0]
      rcases lt_trichotomy j P.natDegree with hj | hj | hj
      · -- If j < n then m > |P.coeff j| + 1, so m + P.coeff j - 1 > 0.
        replace hm := hm j hj
        replace hm : |P.coeff j| < m - 1 := by linarith
        rw [abs_lt] at hm
        linarith
      · -- If j = n then P.coeff j ≥ 1, so m + P.coeff j - 1 > 0.
        rw [hj, ← leadingCoeff]
        linarith
      · -- If j > n then P.coeff j = 0, so m + P.coeff j - 1 > 0 (since m > 1).
        rw [coeff_eq_zero_of_natDegree_lt hj]
        linarith
    · rw [hc1]
      exact zero_lt_one
  -- Show that all coefficients of (X + C m)^k are positive for any k.
  have h2 k : ∀ i ≤ ((X + C m)^k).natDegree, 0 < ((X + C m)^k).coeff i := by
    -- It is enough to show that all coefficients of X + C m are positive.
    apply pos_coeffs_pow
    rw [natDegree_X_add_C]
    intro i hi
    interval_cases i
    · rw [hc0]
      linarith
    · rw [hc1]
      exact zero_lt_one
  -- Let R = ∑ i ∈ range n, (X + C (m + P.coeff i - 1)) * (X + C m) ^ i.
  set R : ℝ[X] := ∑ i ∈ range n, _
  -- Show that all coefficients of R are positive.
  have hR : ∀ i ≤ R.natDegree, 0 < R.coeff i := by
    dsimp [R]
    clear * - hm hn0 h1 h2
    -- Proof by induction on n.
    induction n with
    -- If n = 0 then we get a contradiction with n ≠ 0.
    | zero => contradiction
    | succ n ih =>
      -- Consider n + 1.
      cases n with
      | zero =>
        -- If n = 0 then we need to show that X + C (m + P.coeff 0 - 1) has
        -- positive coefficients. This result follows from h1.
        simp only [zero_add, range_one, sum_singleton, pow_zero, mul_one]
        apply h1
      | succ n =>
        -- If n > 1 then rewrite the sum as
        -- ∑ x ∈ range (n + 1), (X + C (m + P.coeff x - 1)) * (X + C m) ^ x
        --    + (X + C (m + P.coeff (n + 1) - 1)) * (X + C m) ^ (n + 1)
        rw [sum_range_succ]
        apply pos_coeffs_add
        · -- The coefficients of the first polynomial are positive from the induction
          -- hypothesis.
          apply ih
          omega
        · -- The coefficients of the second polynomial are positive because it is
          -- the product of polynomials h1 (n + 1) and h2 (n + 1) with positive coefficients.
          apply pos_coeffs_mul (h1 _)
          apply h2
  -- Q = C (P.coeff n - 1) * (X + C m)^n + R + C 1.
  rw [heq]
  -- C 1 has positive coefficients.
  apply pos_coeffs_add _ (by simp)
  -- Consider two cases: P.coeff n = 1 and P.coeff n ≠ 1.
  by_cases hp1 : P.coeff n = 1
  · -- If P.coeff n = 1 then Q = R + C 1 and both R and C 1 have positive coefficients.
    simp only [hp1, sub_self, map_zero, zero_mul, zero_add]
    exact hR
  -- If P.coeff n ≠ 1, then P.coeff n > 1, so C (P.coeff n - 1) * (X + C m)^n
  -- has positive coefficients.
  apply pos_coeffs_add _ hR
  apply pos_coeffs_mul _ (h2 _)
  rw [natDegree_C]
  simp
  rw [leadingCoeff, hn] at hP1
  rw [lt_iff_le_and_ne]
  exact ⟨by linarith, Ne.symm hp1⟩