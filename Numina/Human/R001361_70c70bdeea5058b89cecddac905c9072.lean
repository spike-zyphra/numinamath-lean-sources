import Mathlib



/- condition for product of positive real numbers reach minimum  -/
lemma l_finset_prod_min {x: ℕ → ℝ} {s: Finset ℕ} {lb: ℝ} (hhs: s.card ≥ 2)
  (lbpos: 0 < lb) (xlb: ∀i ∈ s, x i ≥ lb):
  ∏ i ∈ s, x i ≥ ( (∑ i ∈ s, x i) - (s.card - 1)*lb) * lb^(s.card - 1) := by
  induction' s using Finset.induction_on with j s hj ih
  · simp at hhs
  have sge: s.card ≥ 1 := by
    rw [Finset.card_insert_of_not_mem hj] at hhs
    simpa only [ge_iff_le, Finset.one_le_card,
    Nat.reduceLeDiff] using hhs
  -- base step. if sum a+b is fixed, then ab ≤ lb (a+b - lb), lb is positive lower bound.
  by_cases hs: s.card = 1
  · rw [Finset.card_eq_one] at hs
    rcases hs with ⟨i0, seq⟩
    have hs': ({j, i0}: Finset ℕ).card = 2 := by
      rw [seq] at hj
      simp [Finset.card_insert_of_not_mem hj]
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    simp only [seq, Finset.prod_singleton, Finset.sum_singleton,
    hs', Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, ge_iff_le]
    suffices (x j + x i0) * (x i0 - lb) ≥ (x i0 + lb)*(x i0 - lb) by
      linarith only [this]
    rw [ge_iff_le]
    have h1: lb ≤ x i0 := by
      apply xlb i0
      simp only [seq, Finset.mem_insert, Finset.mem_singleton, or_true]
    have h2: lb ≤ x j := by
      apply xlb j
      simp only [Finset.mem_insert, true_or]
    apply mul_le_mul_of_nonneg_right ?_ ?_
    · linarith only [h2]
    · linarith only [h1]
  -- inductive step.
  replace hs: s.card ≥ 2 := by
    by_contra!
    suffices s.card ≠ 0 by omega
    simp only [Finset.card_insert_of_not_mem hj, ge_iff_le,
    Nat.reduceLeDiff, Finset.one_le_card] at hhs
    exact Finset.card_ne_zero.mpr hhs
  rw [Finset.prod_insert hj]
  have h1: x j * ∏ i ∈ s, x i ≥ x j *
    ( (∑ i ∈ s, x i - (s.card - 1)*lb) * lb^(s.card - 1) ) := by
    have hh1: ∀ i ∈ s, x i ≥ lb := by
      intro i hi
      apply xlb i (Finset.mem_insert_of_mem hi)
    refine mul_le_mul_of_nonneg_left (ih hs hh1) ?_
    linarith only [lbpos, xlb j (Finset.mem_insert_self j s)]
  rw [Finset.sum_insert hj, Finset.card_insert_of_not_mem hj]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
  add_tsub_cancel_right]
  apply le_trans ?_ h1
  have: lb^s.card = lb * lb^(s.card - 1) := by
    rw [← pow_succ']
    congr 1; omega
  rw [this]
  simp only [← mul_assoc]
  rw [mul_le_mul_iff_of_pos_right (pow_pos lbpos _)]
  have h2: ∑ i ∈ s, x i - (s.card - 1)*lb =
    lb + (∑ i ∈ s, x i - s.card * lb) := by ring
  rw [h2, add_sub_assoc, mul_add, add_mul, add_le_add_iff_left]
  rw [mul_comm (x j) _]
  apply mul_le_mul_of_nonneg_left (xlb j (Finset.mem_insert_self _ _)) ?_
  suffices ∑ i ∈ s, x i ≥ ∑ i ∈ s, lb by
    simp only [Finset.sum_const, nsmul_eq_mul] at this
    exact sub_nonneg.mpr this
  exact Finset.sum_le_sum (fun i hi => xlb i (Finset.mem_insert_of_mem hi))

/- an AM-GM for Fin univ. -/
lemma l_geom_mean_le_arith_mean_fin {n: ℕ} (npos: 0 < n)
  {x: Fin n → ℝ} (hx: ∀i, 0 ≤ x i): ∏ i, x i ≤ ((∑ i, x i) / n)^n := by
  suffices hh: (∏i, x i)^(1/n:ℝ) ≤ (∑ i, x i) / n by
    have: ∏ i, x i = ((∏ i, x i)^(1/n:ℝ))^(n:ℕ) := by
      rw [← Real.rpow_mul_natCast]
      simp only [one_div, isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero,
      npos.ne', not_false_eq_true, IsUnit.inv_mul_cancel, Real.rpow_one]
      apply Finset.prod_nonneg (fun i _ => hx i)
    rw [this]
    apply (pow_le_pow_iff_left₀ ?_ ?_ npos.ne').mpr hh
    · apply Real.rpow_nonneg ?_
      apply Finset.prod_nonneg (fun i _ => hx i)
    · apply div_nonneg ?_ (by simp [npos])
      apply Finset.sum_nonneg (fun i _ => hx i)
  set w: ℕ → ℝ := fun i => 1/n with w_def
  have h1: (∏ i, x i)^(1/n:ℝ) = ∏ i, (x i)^(w i) := by
    simp only [w_def]
    rw [Real.finset_prod_rpow _ _ (fun i _ => hx i)]
  have h2: (∑ i, x i) / n = ∑ (i: Fin n), (w i) * (x i) := by
    simp only [w_def]
    rw [Finset.sum_div]
    simp only [one_div, inv_mul_eq_div]
  rw [h1, h2]
  apply Real.geom_mean_le_arith_mean_weighted _ _ _
    (by simp [w_def]) (by simp [w_def, npos.ne']) (fun i _ => hx i)


/- 11. (GDR 1) Given real numbers $x_{1}, x_{2}, \ldots, x_{n}(n \geq 2)$, with $x_{i} \geq 1 / n$ $(i=1,2, \ldots, n)$ and with $x_{1}^{2}+x_{2}^{2}+\cdots+x_{n}^{2}=1$, find whether the product $P=x_{1} x_{2} x_{3} \cdots x_{n}$ has a greatest and/or least value and if so, give these values. -/
theorem algebra_23704 {n : ℕ} (hn : n ≥ 2):
  IsLeast {p | ∃ x : Fin n → ℝ, (∀ i, x i ≥ 1 / n) ∧ (∑ i, (x i)^2 = 1) ∧ p = ∏ i, x i} (Real.sqrt (n^2 - n + 1) / n^n) ∧
  IsGreatest {p | ∃ x : Fin n → ℝ, (∀ i, x i ≥ 1 / n) ∧ (∑ i, (x i)^2 = 1) ∧ p = ∏ i, x i} (1 / n^(n / 2:ℝ)) := by

  have npos: 0 < n := by omega

  constructor

  · -- find minimum value of the product.
    rw [IsLeast]
    constructor

    · -- find a concrete sequence reach minimum.
      -- we claim for the product reach minimum, we take such sequence that
      -- most of them reach lower bound, and the remaining one = sum - lowerbound times (n-1)
      -- here we take first element = √( 1 - (n-1) x (1/n^2) ), the other all reach lowerbound = 1/n.
      simp only [ge_iff_le, Set.mem_setOf_eq]
      use fun (i: Fin n) => if i = ⟨0, npos⟩ then (√(n^2-n+1) / n) else (1/n)
      -- calculations.
      split_ands
      · intro i
        by_cases hi: i = ⟨0, npos⟩
        · simp only [hi, ↓reduceIte]
          rw [div_le_div_iff_of_pos_right (by simp [npos])]
          rw [Real.one_le_sqrt]
          simp only [le_add_iff_nonneg_left, sub_nonneg]
          norm_cast
          apply le_self_pow₀ npos (by norm_num)
        · simp [hi]
      · have: (⟨0, npos⟩: Fin n) ∈ Finset.univ := by
          simp
        rw [← Finset.insert_erase this,
        Finset.sum_insert (Finset.not_mem_erase _ Finset.univ)]
        simp only [↓reduceIte]
        replace: ∑ x ∈ Finset.univ.erase (⟨0, npos⟩: Fin n),
          (if x = ⟨0, npos⟩ then √(↑n ^ 2 - ↑n + 1) / ↑n else 1 / ↑n) ^ 2 =
          ∑ i ∈ Finset.univ.erase (⟨0, npos⟩: Fin n), (1 / n:ℝ)^2 := by
          apply Finset.sum_congr rfl ?_
          intro i hi
          have: i ≠ ⟨0, npos⟩ := Finset.ne_of_mem_erase hi
          simp [this]
        rw [this]
        simp only [inv_pow, Finset.sum_const, Finset.mem_univ,
        Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [div_pow, one_div_pow, Real.sq_sqrt, mul_div_assoc']
        rw [div_add_div_same, Nat.cast_sub (by omega)]
        simp only [Nat.cast_one, mul_one, add_add_sub_cancel, sub_add_cancel, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        Nat.cast_eq_zero, npos.ne', div_self]
        linarith only [sq_nonneg (n-1:ℝ)]
      · have: (⟨0, npos⟩: Fin n) ∈ Finset.univ := by
          simp
        rw [← Finset.insert_erase this,
        Finset.prod_insert (Finset.not_mem_erase _ _)]
        simp only [↓reduceIte]
        rw [Finset.prod_ite_of_false (by simp)]
        simp only [Finset.prod_inv_distrib, Finset.prod_const,
        Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin]
        rw [one_div_pow, mul_one_div, div_div,
        ← pow_succ', Nat.sub_add_cancel (by omega)]

    · -- prove the value is a lower bound.
      simp only [lowerBounds, one_div, ge_iff_le, Set.mem_setOf_eq,
      forall_exists_index, and_imp]
      rintro _ x xge xsum rfl
      -- rewrite Fin univ to Finset range.
      set xx: ℕ → ℝ := fun i => x ⟨i % n, Nat.mod_lt i npos⟩ with xx_def
      have h1: ∏ i, x i = ∏ i ∈ Finset.range n, xx i := by
        suffices ∏ i, x i = ∏ (i: Fin n), xx i by
          rw [this, Fin.prod_univ_eq_prod_range]
        apply Finset.prod_congr rfl ?_
        intro i
        simp only [Finset.mem_univ, forall_const, xx]
        have: i % n = i := Nat.mod_eq_of_lt i.isLt
        congr 1
        exact Fin.eq_mk_iff_val_eq.mpr this.symm
      have h1': ∑ i ∈ Finset.range n, (xx i)^2 = ∑ (i: Fin n), (x i)^2 := by
        suffices ∑ i, (x i)^2 = ∑ (i: Fin n), (xx i)^2 by
          rw [this, ← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl ?_
        intro i
        simp only [Finset.mem_univ, forall_const, xx]
        have: i % n = i := Nat.mod_eq_of_lt i.isLt
        congr 2
        exact Fin.eq_mk_iff_val_eq.mpr this.symm
      have h2: ∏ i ∈ Finset.range n, xx i =
        √(∏ i ∈ Finset.range n, (xx i)^2) := by
        rw [Finset.prod_pow, Real.sqrt_sq]
        apply Finset.prod_nonneg ?_
        intro i hi
        simp only [xx_def, xx]
        apply le_trans ?_ (xge _)
        simp
      have h31: (Finset.range n).card ≥ 2 := by
        simp [hn]
      have h32: 0 < ((n:ℝ)⁻¹)^2 := by simp [npos]
      have h33: ∀i ∈ Finset.range n, (xx i)^2 ≥ ((n:ℝ)⁻¹)^2 := by
        intro i hi
        suffices xx i ≥ (n:ℝ)⁻¹ by
          rwa [ge_iff_le, sq_le_sq₀ (by simp)]
          apply le_trans (by simp) this
        simp [xx_def, xge]
      -- use the lemma we prove before, when sum is fixed, for product reach minimum,
      -- most of the element should take lower bound.
      have h3 := l_finset_prod_min h31 h32 h33
      simp only [Finset.card_range, inv_pow, ge_iff_le] at h3
      simp only [h1', xsum, xx, ← div_eq_mul_inv] at h3
      have h4: 1 - (n-1:ℝ)/n^2 = (n^2-n+1)/n^2 := by
        rw [one_sub_div (by simp [npos.ne'])]
        congr 1; ring
      rw [h4, div_div, ← pow_succ', Nat.sub_add_cancel (by omega)] at h3
      rw [Finset.prod_pow] at h3
      simp only [h1, xx_def, ge_iff_le, xx]
      have h4': 0 ≤ ∏ i ∈ Finset.range n, xx i := by
        apply Finset.prod_nonneg ?_
        intro _ _
        simp only [xx_def]
        apply le_trans ?_ (xge _)
        simp
      rw [← sq_le_sq₀ (by positivity) h4']
      refine le_trans (le_of_eq ?_) h3
      rw [div_pow, Real.sq_sqrt, ← pow_mul, ← pow_mul,
      mul_comm n 2]
      linarith only [sq_nonneg (n-1:ℝ)]

  · -- find maximum value of the product.
    rw [IsGreatest, upperBounds]
    simp only [ge_iff_le, Set.mem_setOf_eq,
    forall_exists_index, and_imp]
    constructor

    · -- provide a sequence reach minimum.
      -- we claim when sum fixed, the product is maximized if every terms are equal.
      use fun i => (1 / √n)
      split_ands
      · intro i
        simp only
        rw [one_div_le_one_div (by simp [npos]) (by simp [npos])]
        refine (Real.sqrt_le_left (by simp)).mpr ?_
        norm_cast
        apply le_self_pow₀ npos (by norm_num)
      · simp only [one_div, inv_pow, Nat.cast_nonneg, Real.sq_sqrt, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, isUnit_iff_ne_zero, ne_eq,
        Nat.cast_eq_zero, npos.ne', not_false_eq_true, IsUnit.mul_inv_cancel]
      · simp only [one_div, Finset.prod_inv_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_inj]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by simp)]
        congr 1
        ring

    · -- prove it's an upper bound
      rintro _ x xge xsum rfl
      have: ∀i, 0 ≤ x i := by
        intro i
        apply le_trans ?_ (xge i)
        simp
      rw [← sq_le_sq₀ (Finset.prod_nonneg (fun i a => this i)) (by positivity)]
      rw [← Finset.prod_pow]
      -- use AM-GM
      replace: ∏ i, (x i)^2 ≤ ((∑ i, (x i)^2) / n)^n := by
        apply l_geom_mean_le_arith_mean_fin npos ?_
        simp only [sq_nonneg, implies_true]
      simp only [xsum, inv_pow] at this
      refine this.trans (le_of_eq ?_)
      simp only [one_div, inv_pow, inv_inj]
      rw [← Real.rpow_mul_natCast (by simp)]
      simp