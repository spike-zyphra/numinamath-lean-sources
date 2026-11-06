import Mathlib

/- Soient un entier $n$ et des réels $0<\mathfrak{u}_{1}<\mathfrak{u}_{2}<\ldots<\boldsymbol{u}_{\boldsymbol{n}}$ tels que

$$
\mathfrak{u}_{1}+\mathfrak{u}_{2}+\ldots+\mathfrak{u}_{n}=\frac{1}{\mathfrak{u}_{1}^{2}}+\frac{1}{\mathfrak{u}_{2}^{2}}+\ldots+\frac{1}{\mathfrak{u}_{n}^{2}}
$$

Montrer que, pour tout entier $k$ inférieur ou égal à $n$, il existe $k$ réels parmi $\mathfrak{u}_{1}, \mathfrak{u}_{2}, \ldots, \mathfrak{u}_{n}$ dont la somme est supérieure ou égale à $k$. -/
theorem algebra_607472 {n : ℕ} (hn : 0 < n) (u : Fin n → ℝ) (upos: 0 < u ⟨0, hn⟩)
    (hu : StrictMono u) (hsum : ∑ i : Fin n, u i = ∑ i : Fin n, 1 / u i ^ 2) :
    ∀ k : ℕ, k ≤ n → ∃ s : Finset (Fin n),
      s.card = k ∧ ∑ i ∈ s, u i ≥ k := by

  replace upos: ∀i, 0 < u i := by
    intro i
    apply lt_of_lt_of_le upos ?_
    by_cases hi: i = ⟨0,hn⟩
    · simp [hi]
    · replace hi: ⟨0,hn⟩ < i := by
        refine Fin.mk_lt_of_lt_val ?_
        refine Nat.zero_lt_of_ne_zero ?_
        rintro heq
        absurd hi
        exact Fin.eq_mk_iff_val_eq.mpr heq
      apply le_of_lt (hu hi)

  set w: ℕ → ℝ := fun i => 1/n with w_def
  have unng: ∀ i, 0 ≤ u i := fun i  => (upos i).le
  have hn': (@Finset.univ (Fin n)).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact Fin.pos_iff_nonempty.mp hn

  -- by AM-GM, (u1+u2+...+un)/n ≥ (u1 u2 ... un)^(1/n)
  have am_gm1: (∑ i, u i)/n ≥ (∏ i, (u i))^(1/n:ℝ) := by
    have h1: (∑ i, u i)/n = ∑ (i: Fin n), (w i) * (u i) := by
      simp only [w_def]
      rw [← Finset.mul_sum, mul_comm, mul_one_div]
    have h2: (∏ i, (u i))^(1/n:ℝ) = ∏ i, (u i)^(w i) := by
      simp only [w_def]
      rw [Real.finset_prod_rpow _ _ (by simp [unng])]
    rw [h1, h2]
    apply Real.geom_mean_le_arith_mean_weighted _ _ _ ?_ ?_ ?_
    <;> simp [w_def, hn.ne', unng]

  -- similarly, (1/u1^2 + 1/u2^2 + ... + 1/un^2) / n ≥ (1/u1^2 1/u2^2 ... 1/un^2)^(1/n)
  have am_gm2: (∑ i, (1 / (u i)^2)) / n ≥ 1 / ((∏ i, (u i))^(1/n:ℝ))^2 := by
    have h1: (∑ i, (1 / (u i)^2)) /(n:ℝ) = ∑ (i: Fin n), ((w i) * (1 / (u i)^2)) := by
      simp only [w_def]
      rw [← Finset.mul_sum, mul_comm, mul_one_div]
    have h2: 1 / ((∏ i, (u i))^(1/n:ℝ))^2 = ∏ i, (1 / (u i)^2)^(w i) := by
      rw [← Real.rpow_mul_natCast (Finset.prod_nonneg (by simp [unng]))]
      simp only [w_def]
      rw [← Real.finset_prod_rpow _ _ (by simp [unng])]
      rw [one_div, ← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl (fun i _ => ?_)
      rw [← one_div_pow, ← Real.rpow_natCast_mul (by simp [unng])]
      rw [← Real.rpow_neg (unng i), one_div (u i), ← Real.rpow_neg_one,
      ← Real.rpow_mul (unng i)]
      congr 1; ring
    rw [h1, h2]
    apply Real.geom_mean_le_arith_mean_weighted _ _ _ ?_ ?_ ?_
    <;> simp [w_def, hn.ne', unng]

  -- thus we claim u1 + u2 + ... + un ≥ n.
  have case_n: (∑ i, u i) / n ≥ 1 := by
    -- if a ≥ 1/a^2, then a ≥ 1.
    have h1 {a: ℝ} (ha: a ≥ 1/a^2) (apos: 0 < a): a ≥ 1 := by
      have a2pos: 0 < a^2 := pow_pos apos 2
      replace ha: a^2 * a ≥ a^2 * (1 / a^2) := by
        exact (mul_le_mul_iff_of_pos_left a2pos).mpr ha
      simp only [one_div, mul_inv_cancel₀ a2pos.ne'] at ha
      rwa [← pow_succ, ge_iff_le,
      one_le_pow_iff_of_nonneg apos.le (by norm_num)] at ha
    -- if a ≥ g, then 1/g^2 ≥ 1/a^2
    have h2 {a g: ℝ} (apos: 0 < a) (gpos: 0 < g)
      (hag: a ≥ g): 1/g^2 ≥ 1/a^2 := by
      have: a^2 ≥ g^2 := (sq_le_sq₀ gpos.le apos.le).mpr hag
      refine one_div_le_one_div_of_le ?_ this
      exact pow_pos gpos 2
    have apos: 0 < (∑ i, u i)/n := by
      apply div_pos ?_ (by simp [hn])
      apply Finset.sum_pos (by simp [upos]) hn'
    have gpos: 0 < (∏ i, (u i))^(1/n:ℝ) := by
      apply Real.rpow_pos_of_pos ?_ _
      apply Finset.prod_pos (by simp [upos])
    -- use AM-GM we proved above.
    apply h1 ?_ apos
    nth_rw 1 [hsum]
    apply le_trans ?_ am_gm2
    apply h2 apos gpos am_gm1
  replace case_n := (one_le_div₀ (by simp [hn])).mp case_n

  -- so the relation holds when k=n. and we claim it must hold for all k < n.
  -- if it not hold for k = n-1, then it's not true for k=n either.
  have {t: Finset (Fin n)} (tnz: t.Nonempty) (htc: 1 < t.card)
    (h: ∀s: (Finset (Fin n)), s.card = t.card - 1 → ∑ i ∈ s, u i < t.card-1):
    ∑ i ∈ t, u i < t.card := by
    have tcpos: 0 < t.card := Finset.card_pos.mpr tnz
    -- denote t.card by m.
    -- from given condition,
    -- u1+u2+...+u_{m-1} < m-1, v2+...+v_m < m-1, ..., v_m+v_1+..+v_{m-2} < m-1.
    -- add them together, (m-1)(v1+v2+...+vm) < m(m-1), thus v1+v2+...+vm < m.
    have h1: ∑ i ∈ t, (∑ j ∈ t.erase i, u j) < ∑ i ∈ t, (t.card - 1:ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty tnz
      intro i hi
      apply h _ ?_
      rw [Finset.card_erase_of_mem hi]
    have h2: ∑ i ∈ t, (∑ j ∈ t.erase i, u j) =
      ∑ i ∈ t, (∑ j ∈ t, u j) - ∑ i ∈ t, u i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl (fun _ hi => ?_)
      exact Finset.sum_erase_eq_sub hi
    -- to prove the sum < m, suffices to show (m-1)sum < m(m-1)
    have h3 {a:ℝ} (ha: t.card*a-a < t.card*t.card - t.card): a < t.card := by
      have hh1: t.card*a-a = a*(t.card-1) := by ring
      have hh2: 0 < (t.card-1:ℝ) := by
        rify at htc
        exact sub_pos.mpr htc
      rw [hh1, ← mul_sub_one] at ha
      exact (mul_lt_mul_iff_of_pos_right hh2).mp ha
    apply h3
    rw [h2] at h1
    simpa [mul_sub_one] using h1

  -- then use induction.
  replace: ∀j, j < n → ∃ s : Finset (Fin n), s.card = n-j ∧ ∑ i ∈ s, u i ≥ n-j := by
    intro j hj
    induction' j with j ih
    · use (@Finset.univ (Fin n) (Fin.fintype n))
      simp [case_n]
    · by_contra! hh
      have jltn: j < n := Nat.lt_of_succ_lt hj
      rcases (ih jltn) with ⟨t,ht1, ht2⟩
      absurd ht2
      push_neg
      have tnz: t.Nonempty := by
        apply Finset.card_pos.mp
        simp [ht1, jltn]
      have h1: n-(j+1) = t.card - 1 := by
        rw [ht1, Nat.sub_sub]
      have h2: n - (↑(j+1):ℝ) = t.card - 1 := by
        rify at h1
        rw [Nat.cast_sub hj.le, Nat.cast_sub (Finset.one_le_card.mpr tnz)] at h1
        simpa using h1
      replace hj: 1 < n-j := Nat.lt_sub_iff_add_lt'.mpr hj
      rw [← ht1] at hj
      rify at ht1
      rw [Nat.cast_sub jltn.le] at ht1
      rw [← ht1]
      apply this tnz hj ?_
      rwa [← h1, ← h2]

  -- thus finish.
  intro k hk
  by_cases k0: k = 0
  · simp [k0]
  have kpos: 0 < k := Nat.zero_lt_of_ne_zero k0
  specialize this (n-k) (Nat.sub_lt hn kpos)
  simpa [Nat.sub_sub_self hk, Nat.cast_sub hk, sub_sub_cancel] using this