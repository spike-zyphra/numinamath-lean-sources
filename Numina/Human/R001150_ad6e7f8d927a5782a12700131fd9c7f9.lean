import Mathlib

/- Let $Q$ be a polynomial \[Q(x)=a_0+a_1x+\cdots+a_nx^n,\]where $a_0,\ldots,a_n$ are nonnegative integers.
Given that $Q(1)=4$ and $Q(5)=152$, find $Q(6)$. -/
theorem algebra_20751 {Q : Polynomial ℤ} (hQ : ∀ n, Q.coeff n ≥ 0)
    (hQ1 : Q.eval 1 = 4) (hQ2 : Q.eval 5 = 152) : Q.eval 6 = 254 := by
  -- since all coefficients are non-negative, Q ≥ corresponding coeff times x^n
  have h1(n:ℕ)(m:ℕ): Q.eval ↑m ≥ (Q.coeff n) * m^n := by
    have hh1: Q = Q.erase n + ((Q.coeff n) * ↑Polynomial.X^n) := by
      rw [Polynomial.ext_iff]
      intro n'
      by_cases hn: n'=n
      <;> simp [hn]
    nth_rw 1 [hh1]; simp
    rw [Polynomial.eval_eq_sum]
    apply Finset.sum_nonneg
    intro i _; simp [hQ]
    apply mul_nonneg
    · by_cases hn: i = n
      · rw [hn]; simp
      · rw [Polynomial.erase_ne _ _ _ hn]
        apply hQ
    · simp
  -- therefore degree of Q ≤ 3, otherwise Q 5 > 152
  have h2: Q.degree ≤ 3 := by
    by_contra! hc
    replace hc: Q.degree ≥ 4 := by
      exact Order.le_of_pred_lt hc
    have hh1: Q.eval 5 ≥ Q.coeff Q.natDegree * 5^Q.natDegree := by
      apply h1
    have hh2: Q.coeff Q.natDegree * 5^Q.natDegree ≥ 625 := by
      have tt1: Q.coeff Q.natDegree ≥ 1 := by
        have: Q.coeff Q.natDegree > 0 := by
          have htt1: Q.coeff Q.natDegree ≠ 0 := by
            have: Q ≠ 0 := by
              by_contra! hc; rw [hc] at hQ1; simp at hQ1
            simp [this]
          exact lt_of_le_of_ne (hQ Q.natDegree) (id (Ne.symm htt1))
        exact this
      have tt2: Q.natDegree ≥ 4 := by
        exact Polynomial.le_natDegree_of_coe_le_degree hc
      have tt3: (5:ℤ)^Q.natDegree ≥ 625 := by
        have: (625:ℤ) = 5^4 := by norm_num
        rw [this]
        apply (pow_le_pow_iff_right (by norm_num)).mpr tt2
      rw [← one_mul 625]
      apply mul_le_mul tt1 tt3 (by norm_num) (by linarith [tt1])
    have hh3: (625:ℤ) ≤ 152 := by
      rw [hQ2] at hh1
      apply le_trans hh2 hh1
    linarith [hh3]
  -- so Q = a3x^3+a2x^2+a1x+a0
  let a3:ℤ := Q.coeff 3
  have a3_def: a3 = Q.coeff 3 := rfl
  have a3_nng: 0 ≤ a3 := by
    apply hQ
  let a2:ℤ := Q.coeff 2
  have a2_def: a2 = Q.coeff 2 := rfl
  have a2_nng: 0 ≤ a2 := by
    apply hQ
  let a1:ℤ := Q.coeff 1
  have a1_def: a1 = Q.coeff 1 := rfl
  have a1_nng: 0 ≤ a1 := by
    apply hQ
  let a0:ℤ := Q.coeff 0
  have a0_def: a0 = Q.coeff 0 := rfl
  have a0_nng: 0 ≤ a0 := by
    apply hQ
  have hq_def: Q = a3*↑Polynomial.X^3 + a2*↑Polynomial.X^2 +
    a1 * ↑Polynomial.X + a0 := by
    rw [a3_def, a2_def, a1_def, a0_def]
    rw [Polynomial.ext_iff]; intro n
    have hz{m m':ℕ}(hm: m ≠ 0): (Q.coeff m': Polynomial ℤ).coeff m = 0 := by
      apply Polynomial.coeff_C_ne_zero hm
    by_cases hn: n > 3
    · simp
      rw [if_neg, if_neg]; any_goals linarith [hn]
      have hh1: Q.coeff 1 * Polynomial.X.coeff n = 0 := by
        simp; right
        apply Polynomial.coeff_eq_zero_of_degree_lt
        simp; linarith [hn]
      rw [hh1]; simp
      have hh2: Q.coeff n = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        apply lt_of_le_of_lt h2
        simp [hn]
      rw [hh2, hz]
      linarith [hn]
    · push_neg at hn
      interval_cases n <;> simp
      · apply Polynomial.coeff_C_ne_zero (by simp)
      · rw [hz (by simp), hz (by simp)]; simp
      · rw [hz (by simp), hz (by simp)]; simp
  -- from Q(1) = 4 and Q(5) = 152, we may find equations of a0,a1,a2,a3 and determine Q(6)
  have eq1: a0+a1+a2+a3 = 4 := by
    rw [← hQ1, hq_def]; simp; ring
  -- since they are all non-negative, each of them ≤ 4
  have ha0: a0 ≤ 4 := by
    rw [← eq1]; linarith [a1_nng, a2_nng, a3_nng]
  have ha1: a1 ≤ 4 := by
    rw [← eq1]; linarith [a0_nng, a2_nng, a3_nng]
  have eq2: 125*a3+25*a2+5*a1+a0 = 152 := by
    rw [← hQ2, hq_def]; simp; ring
  -- so a3 must be 1. if a3 >1, 125a3 > 152, contradiction. and if a3 = 0, for a2,a1,a0 ≤ 4
  -- 25a2+5a1+a0 cannnot reach 152.
  have a3eq: a3 = 1 := by omega
  -- then 25a2+5a1+a0 = 27
  -- similarly, from eq3, we can determine a2=1
  have a2eq: a2 = 1 := by omega
  -- then 5a1+a0 = 2, only solution is a1=0 and a0=2
  have a1eq: a1 = 0 := by omega
  have a0eq: a0 = 2 := by omega
  -- thus Q is determined, and we can calculate Q(6)
  --Q(6) = 6^3+6^2+2=216+36+2=254
  rw [hq_def, a3eq, a2eq, a1eq, a0eq]
  simp