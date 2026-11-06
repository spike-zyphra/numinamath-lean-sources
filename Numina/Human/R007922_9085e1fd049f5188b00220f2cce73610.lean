import Mathlib

/- A sequence $\left(a_{n}\right)$ is defined as follows: $a_{1}=\sqrt{2}, a_{2}=2$, and $a_{n+1}=a_{n} a_{n-1}^{2}$ for $n \geq 2$. Prove that for every $n \geq 1$ we have

$$
\left(1+a_{1}\right)\left(1+a_{2}\right) \cdots\left(1+a_{n}\right)<(2+\sqrt{2}) a_{1} a_{2} \cdots a_{n} .
$$ -/
theorem inequalities_236767 {a : ℕ → ℝ}
    (ha0 : a 0 = √2) (ha1 : a 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = a n * (a (n - 1))^2) :
    ∀ n, n ≥ 1 →
    ∏ i ∈ Finset.range n, (1 + a i) < (2 + √2) * ∏ i ∈ Finset.range n, a i := by
  -- by induction, we can prove a n = 2 ^ (2^(n-1))
  have ha{n:ℕ}(hn: n ≥ 1): a n = 2 ^ (2 ^ (n-1)) := by
    induction' n using Nat.strong_induction_on with n ih
    by_cases hn1: n = 1
    · simp [hn1, ha1]
    replace hn: n ≥ 2 := by omega
    have h1: n = n-1+1 := by omega
    have h2: n-1 ≥ 1 := by omega
    nth_rw 1 [h1, han (n-1) h2]
    by_cases hn2: n = 2
    · simp only [hn2, Nat.add_one_sub_one, ha1,
      tsub_self, ha0, Nat.ofNat_nonneg, Real.sq_sqrt,
      pow_one]
      norm_num
    replace hn: n ≥ 3 := by omega
    have h3: n-1-1 ≥ 1 := by omega
    rw [ih (n-1) (by omega) h2, ih (n-1-1) (by omega) h3]
    rw [← pow_mul, ← pow_add]
    congr 1
    rw [← pow_succ, Nat.sub_add_cancel h3,
    ← mul_two, ← pow_succ, Nat.sub_add_cancel h2]
  intro n hn
  -- since 1+a0 = 1+√2, it suffcies to show
  -- (1+a1)(1+a2)...(1+a_{n-1}) < 2 a1a2...a_{n-1}
  suffices ∏ i ∈ Finset.range (n-1), (1 + a (1+i)) <
    2 * ∏ i ∈ Finset.range (n-1), a (1+i) by
    rw [← Nat.sub_add_cancel hn, add_comm _ 1]
    simp only [Finset.prod_range_add, Finset.range_one,
    Finset.prod_singleton, add_zero, ha0, ← mul_assoc]
    -- (2+√2) √2 = 2 (1+√2)
    have hh: (2+√2)*√2 = (1+√2) * 2 := by
      rw [add_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
      ring
    rw [hh, mul_assoc]
    apply mul_lt_mul_of_pos_left this
    positivity
  -- use induction, right hand side is 2 ^ (2 ^ (n-1) )
  have rhs: 2 * ∏ i ∈ Finset.range (n-1), a (1+i) = 2^(2^(n-1)) := by
    induction' n,hn using Nat.le_induction with n hn ih
    · simp
    · have: n+1-1 = n-1 + 1 := by simp [hn]
      rw [this, Finset.prod_range_succ,
      ← mul_assoc, ih, add_comm 1 (n-1)]
      rw [Nat.sub_add_cancel hn, ha hn, ← pow_add]
      congr 1
      nth_rw 3 [← Nat.sub_add_cancel hn]
      rw [pow_succ]
      ring
  -- and left side is 2^(2^(n-1))-1
  have lhs: ∏ i ∈ Finset.range (n-1), (1 + a (1+i)) = 2^(2^(n-1)) - 1 := by
    -- to prove this, we show prod 1+an can be written as a sum of geom sequence.
    have: ∏ i ∈ Finset.range (n-1), (1 + a (1+i)) =
      ∑ i ∈ Finset.range (2^(n-1)), 2^i := by
      clear * - ha hn
      induction' n,hn using Nat.le_induction with n hn ih
      · simp
      · have: n+1-1 = n-1 + 1 := by simp [hn]
        rw [this, Finset.prod_range_succ, ih, pow_succ, mul_two,
        Finset.sum_range_add, mul_add, mul_one, add_right_inj]
        rw [Finset.sum_mul]; congr 1
        funext i
        rw [ha (by simp), ← pow_add, add_comm i _]
        congr 3
        simp [hn]
    -- therefore left side is geometric sequence sum, use geom sum formula.
    rw [this, geom_sum_eq (by norm_num)]
    norm_num
  -- thus left side = right side - 1, done.
  rw [lhs, rhs]
  simp