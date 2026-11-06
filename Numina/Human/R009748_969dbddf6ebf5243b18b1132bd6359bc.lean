import Mathlib

/- Let $n$ be a positive integer and let $a_{1}, \ldots, a_{n}$ be
real numbers satisfying $0 \leq a_{i} \leq 1$ for $i=1, \ldots, n$.
Prove the inequality
$$
\left(1-a_{1}^{n}\right)\left(1-a_{2}^{n}\right) \cdots\left(1-a_{n}^{n}\right) \leq\left(1-a_{1} a_{2} \cdots a_{n}\right)^{n} .
$$-/
theorem inequalities_605515{n: ℕ}(npos: 0 < n)(a: Fin n → ℝ)
  (ha: ∀i, (0 ≤ a i ∧ a i ≤ 1)):
  ∏i, (1 - (a i)^n) ≤ (1 - ∏i, a i)^n := by
  -- before start, we write several lemmas about AM-GM.
  set w: ℕ → ℝ := fun i => 1/n with w_def
  have w_nng: ∀i ∈ Finset.range n, 0 ≤ w i := by simp [w_def]
  have w_sum: ∑i ∈ Finset.range n, w i = 1 := by simp [w_def, npos.ne']
  -- by AM-GM, b1b2...bn ≤ ((b1+b2+..+bn)/n)^n
  have lemma_amgm1{b: Fin n → ℝ}(b_nng: ∀i, 0 ≤ b i):
    ∏i, (b i)^(1/n: ℝ) ≤ (∑i, b i)/n := by
    set bb: ℕ → ℝ := fun i => b ⟨i % n, Nat.mod_lt i npos⟩ with bb_def' 
    have bb_def: ∀i, b i = bb i := by
      simp [bb_def']; intro i; congr
      simp [Nat.mod_eq_of_lt]
    have bb_nng: ∀i ∈ Finset.range n, 0 ≤ bb i := by
      simp [bb_def', b_nng]
    have := Real.geom_mean_le_arith_mean_weighted
      _ w bb w_nng w_sum bb_nng
    have h1: ∏i, b i^(1/n:ℝ) = ∏(i: Fin n), bb i^(1/n: ℝ) := by
      congr; simp [bb_def]
    simp only [← Fin.prod_univ_eq_prod_range, 
    ← Fin.sum_univ_eq_sum_range, w_def, ← h1] at this
    rw [← Finset.mul_sum] at this
    apply le_trans this (le_of_eq ?_)
    field_simp [npos]; simp [bb_def]
  -- take nth power for both sides at above lemma
  have lemma_amgm2{b: Fin n → ℝ}(b_nng: ∀i, 0 ≤ b i):
    ∏i, b i ≤ ((∑i, b i)/n)^n := by
    have: ∏i, b i = (∏i, (b i)^(1/n:ℝ))^n := by
      rw [Real.finset_prod_rpow, ← Real.rpow_mul_natCast]
      simp [npos.ne']
      · apply Finset.prod_nonneg
        simp [b_nng]
      · simp [b_nng]
    rw [this]
    apply pow_le_pow_left₀ ?_ ?_
    · apply Finset.prod_nonneg
      intro i _
      apply b_nng i |> Real.rpow_nonneg
    · apply lemma_amgm1 b_nng
  -- back to the problem, use AM-GM, following inequality holds.
  have h1: ∏i, (1 - (a i)^n) ≤ (1 - (∑i, (a i)^n)/n)^n := by
    set b: Fin n → ℝ := fun i => 1 - (a i)^n with b_def
    have b_nng: ∀i, 0 ≤ b i := by
      intro i; simp [b_def]
      apply pow_le_one₀ (ha i).left (ha i).right
    -- b1b2...bn ≤ ((b1+b2+...+bn / n))^n
    apply le_trans (lemma_amgm2 b_nng) ?_
    apply pow_le_pow_left₀ ?_ ?_
    · apply div_nonneg ?_ (by simp)
      apply Finset.sum_nonneg
      simp [b_nng]
    · apply le_of_eq
      field_simp
      simp [b_def]
  -- use AM-GM again, (a1^n+a2^n+..+an^n)/n ≥ a1a2...an
  have h2: (∑i, (a i)^n)/n ≥ ∏i, a i := by
    -- view (ai)^n as a series
    have an_nng: ∀i, 0 ≤ (a i)^n := by
      intro i; apply pow_nonneg
      simp [ha]
    apply le_trans (le_of_eq ?_) (lemma_amgm1 an_nng)
    congr 1; funext _
    rw [← Real.rpow_natCast_mul (by simp [ha])]
    simp [npos.ne']
  -- therefore following holds.
  have h3: (1 - (∑i, (a i)^n)/n)^n ≤ (1 - ∏i, a i)^n := by
    apply pow_le_pow_left₀ ?_ ?_
    · field_simp
      apply div_nonneg ?_ (by simp)
      have: (n:ℝ) = ∑ (i:Fin n), 1 := by simp
      rw [this]
      apply sub_nonneg.mpr
      apply Finset.sum_le_sum (fun i _ => ?_)
      apply pow_le_one₀ (ha i).left (ha i).right
    · linarith [h2]
  -- done.
  apply le_trans h1 h3