import Mathlib


/- if s.max = s.min, then s.card = 1  -/
lemma l_finset_card_eq_one_of_max_eq_min
  {α : Type*} [LinearOrder α] {s: Finset α} {a b: α}
  (ha: s.max = a) (hb: s.min = b)
  (heq: a = b): s.card = 1 := by
  rw [Finset.card_eq_one]
  use a
  ext x
  simp only [Finset.mem_singleton]
  constructor
  · intro hx
    apply le_antisymm
    · exact Finset.le_max_of_eq hx ha
    · rw [heq]
      exact Finset.min_le_of_eq hx hb
  · intro h
    rw [h]
    exact Finset.mem_of_max ha


/- if each element of s has distance ≥ d, then s.max - s.min ≥ d (#s-1)  -/
lemma l_max_ge_dist_mul_card_add_min {α: Type*} {d: α} {s: Finset α}
  [LinearOrderedCommSemiring α]
  (hs: s.card ≥ 2)
  (hd: ∀a ∈ s, ∀ b ∈ s, a > b → a ≥ b+d):
  ∀x:α, s.max = x → ∀y:α, s.min = y → x ≥ (s.card - 1) • d + y := by
  induction' s using Finset.strongInductionOn with s ih
  intro x hx
  have snz: (s.erase x).Nonempty := by
    refine Finset.Nontrivial.erase_nonempty ?_
    exact Finset.one_lt_card_iff_nontrivial.mp hs
  have x_mem: x ∈ s := Finset.mem_of_max hx
  rcases (Finset.max_of_nonempty snz) with ⟨z, hz⟩
  intro y hy
  have ynex: y ≠ x := by
    by_contra!
    replace: s.card = 1 := by
      apply l_finset_card_eq_one_of_max_eq_min hx hy this.symm
    norm_num [this] at hs
  have y_mem: y ∈ (s.erase x) := by
    refine Finset.mem_erase_of_ne_of_mem ynex ?_
    exact Finset.mem_of_min hy
  rcases (Finset.min_of_nonempty snz) with ⟨y', hy'⟩
  have: y' = y := by
    apply le_antisymm
    · apply Finset.min_le_of_eq y_mem hy'
    · refine Finset.min_le_of_eq ?_ hy
      exact Finset.mem_of_mem_erase <| Finset.mem_of_min <| hy'
  rw [this] at hy'
  by_cases hyz: y = z
  · have: (s.erase x).card = 1 :=
      l_finset_card_eq_one_of_max_eq_min hz hy' hyz.symm
    rw [Finset.card_erase_of_mem x_mem] at this
    rw [show s.card = 2 by omega]
    simp only [Nat.add_one_sub_one, mul_one, ge_iff_le, one_smul]
    rw [add_comm d y]
    apply hd x x_mem y (Finset.mem_of_mem_erase y_mem)
    apply lt_of_le_of_ne ?_ ynex
    exact Finset.min_le_of_eq x_mem hy
  · push_neg at hyz
    have: (s.erase x).card ≥ 2 := by
      by_contra!
      replace: (s.erase x).card ≤ 1 := by
        exact Nat.le_of_lt_succ this
      rw [Finset.card_le_one] at this
      specialize this y y_mem z (Finset.mem_of_max hz)
      simp [this] at hyz
    specialize ih (s.erase x) (Finset.erase_ssubset x_mem) this
    replace: ∀ a ∈ s.erase x, ∀b ∈ s.erase x, a > b → a ≥ b + d := by
      intro a ha b hb
      apply hd a ?_ b ?_
      all_goals apply Finset.mem_of_mem_erase (by assumption)
    specialize ih this z hz y hy'
    rw [Finset.card_erase_of_mem x_mem] at ih
    have z_mem := Finset.mem_of_mem_erase (Finset.mem_of_max hz)
    have xgtz: x > z := by
      apply lt_of_le_of_ne ?_ ?_
      · exact Finset.le_max_of_eq z_mem hx
      · rintro heq
        have: z ∈ s.erase x := Finset.mem_of_max hz
        simp [heq] at this
    specialize hd x x_mem z z_mem xgtz
    simp [nsmul_eq_mul] at ih ⊢
    refine le_trans ?_ hd
    have: ↑(s.card - 1) * d = ↑(s.card - 1 - 1)*d + d := by
      simp only [← nsmul_eq_mul]
      have: s.card - 1 = s.card -1 - 1 + 1 := by omega
      nth_rw 1 [this, add_nsmul]
      simp only [nsmul_eq_mul, one_smul]
    rw [this, add_comm _ d, add_assoc d _ _, add_comm d _]
    exact add_le_add_right ih d


/- if natural number set s has an upper bound u, each elements have distance ≥ d,
then we have d (#s - 1) ≤ u.  -/
lemma l_dist_mul_card_le_upper_bound_nat {s: Finset ℕ} {d u: ℕ}
  (hub: ∀i ∈ s, i ≤ u)
  (hd: ∀a ∈ s, ∀b ∈ s, a > b → a - b ≥ d):
  d * (s.card - 1) ≤ u := by
  by_cases hs: s.card ≤ 1
  · simp [hs]
  · replace hs: s.card ≥ 2 := by omega
    have snz: s.Nonempty := Finset.card_pos.mp
      <| Nat.zero_lt_of_lt <| hs
    rcases (Finset.max_of_nonempty snz) with ⟨x, hx⟩
    rcases (Finset.min_of_nonempty snz) with ⟨y, hy⟩
    have h1: x ≤ u := hub x (Finset.mem_of_max hx)
    have h2: d * (s.card - 1) ≤ (s.card - 1) • d + y := by
      simp [mul_comm _ d]
    refine le_trans h2 (le_trans  ?_ h1)
    replace hd: ∀a ∈ s, ∀b ∈ s, a > b → a ≥ b + d :=
      fun a ha b hb hab =>
        (Nat.le_sub_iff_add_le' hab.le).mp (hd a ha b hb hab)
    apply l_max_ge_dist_mul_card_add_min hs hd x hx y hy


/- if nonnegative rational number set s, each elements' distance ≥ d,
upper bound is u, then d (#s - 1) ≤ u.  -/
lemma l_dist_mul_card_le_upper_bound_rat {s: Finset ℚ} {d u: ℚ}
  (hub: ∀i ∈ s, i ≤ u) (hlb: ∀i ∈ s, 0 ≤ i) (upos: 0 < u) (dpos: 0 < d)
  (hd: ∀a ∈ s, ∀b ∈ s, a > b → a - b ≥ d):
  d * (s.card - 1) ≤ u := by
  by_cases hs: s.card ≤ 1
  · refine le_of_lt <| lt_of_le_of_lt ?_ upos
    apply mul_nonpos_of_nonneg_of_nonpos dpos.le (by simp [hs])
  · replace hs: s.card ≥ 2 := by omega
    have snz: s.Nonempty := Finset.card_pos.mp
      <| Nat.zero_lt_of_lt <| hs
    rcases (Finset.max_of_nonempty snz) with ⟨x, hx⟩
    rcases (Finset.min_of_nonempty snz) with ⟨y, hy⟩
    have h1: x ≤ u := hub x (Finset.mem_of_max hx)
    have h2: d * (s.card - 1) ≤ (s.card - 1) • d + y := by
      simp only [nsmul_eq_mul, mul_comm _ d]
      rw [Nat.cast_sub (by omega)]
      simp [hlb y (Finset.mem_of_min hy)]
    refine le_trans h2 (le_trans  ?_ h1)
    replace hd: ∀a ∈ s, ∀b ∈ s, a > b → a ≥ b + d :=
      fun a ha b hb hab =>
        (by linarith only [hd a ha b hb hab])
    apply l_max_ge_dist_mul_card_add_min hs hd x hx y hy

/- if any two elements in the set are congruent modulo n,
then it can be covered by an arithmetic sequence. -/
lemma l_ar_prog_cover (p:ℕ) {f: ℕ → Prop} [DecidablePred f] (pge: p ≥ 2)
  (s: Finset ℕ)
  (hs: ∀i ∈ s.filter f, ∀j ∈ s.filter f, i ≡ j [MOD p]):
  ∃ x0, x0 < p ∧
  s.filter f ⊆ (s.filter (p ∣ · - x0)).filter (· ≥ x0) := by
  have ppos: 0 < p := by exact Nat.zero_lt_of_lt pge
  by_cases hz: s.filter f = ∅
  · simp only [hz, Finset.not_mem_empty, IsEmpty.forall_iff,
    implies_true, Finset.empty_subset, and_self, and_true]
    use 0,ppos
  · replace hz: (s.filter f).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hz
    rcases (Finset.min_of_nonempty hz) with ⟨y0, hy0⟩
    have y0_mem: y0 ∈ s.filter f := Finset.mem_of_min hy0
    use y0 % p
    simp only [Nat.mod_lt _ ppos, true_and]
    intro y hy
    simp only [ge_iff_le, Finset.mem_filter]
    refine ⟨⟨Finset.mem_of_mem_filter y hy, ?_⟩, ?_⟩
    · specialize hs y0 y0_mem y hy
      nth_rw 1 [← Nat.div_add_mod y p, hs]
      simp
    · refine le_trans (Nat.mod_le y0 p) ?_
      exact Finset.min_le_of_eq hy hy0

/- if s1 ⊆ t1, s2 ⊆ t2, s3 ⊆ t3, then s union ⊆ t union   -/
lemma l_finset_union_subset_union_3 {s1 s2 s3 t1 t2 t3: Finset ℕ}
  (h1: s1 ⊆ t1) (h2: s2 ⊆ t2) (h3: s3 ⊆ t3):
  s1 ∪ s2 ∪ s3 ⊆ t1 ∪ t2 ∪ t3 := by
  refine Finset.union_subset_union ?_ h3
  exact Finset.union_subset_union h1 h2

/- Let $n \geqslant 2018$ be an integer, and let $a_{1}, a_{2}, \ldots, a_{n}, b_{1}, b_{2}, \ldots, b_{n}$ be pairwise distinct positive integers not exceeding $5 n$.
Suppose that the sequence  $$ \frac{a_{1}}{b_{1}}, \frac{a_{2}}{b_{2}}, \ldots, \frac{a_{n}}{b_{n}} $$  forms an arithmetic progression. Prove that the terms of the sequence are equal.  (Thailand) -/
theorem number_theory_23684 {n : ℕ} (hn : 2018 ≤ n) (a b : ℕ → ℕ)
    (a_distinct : ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n,
      a i = a j → i = j)
    (b_distinct : ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n,
      b i = b j → i = j)
    (apos : ∀ i ∈ Finset.Icc 1 n, 0 < a i)
    (bpos: ∀ i ∈ Finset.Icc 1 n, 0 < b i)
    (ale5n: ∀ i ∈ Finset.Icc 1 n, a i ≤ 5*n)
    (ble5n: ∀i ∈ Finset.Icc 1 n, b i ≤ 5*n)
    (harprog : ∃ d:ℚ, ∀ i ∈ Finset.Icc 1 n,
      a i / b i = a 1 / b 1 + d * (i-1)) :
    ∃ (x:ℚ), ∀ i ∈ Finset.Icc 1 n, a i / b i = x := by

  -- before start, we write down some trivial calculations that will be used later.
  have npos: 0 < n := by omega
  have cal1 {p s: ℕ} (pge: p ≥ 7) (hs: s ≥ 2 → p * s ≤ n + p):
    ¬ p*n ≤ 5*n + p + p * s := by
    have ppos: 0 < p := by omega
    have hp1: (p-5)*n > 2*p := by
      by_cases hh: p ≤ 10
      · have hh1: (p-5)*n > 1*n := mul_lt_mul_of_pos_right
          (Nat.lt_sub_of_add_lt pge) npos
        refine lt_trans ?_ hh1
        simp only [one_mul]
        refine lt_of_lt_of_le ?_ hn
        linarith only [hh]
      · push_neg at hh
        suffices 2 * ((p-5)*n) > 2 * (2*p) by
          simpa only [gt_iff_lt, Nat.ofNat_pos, mul_lt_mul_left] using this
        have hh1: 2 * ((p-5)*n) > p * n := by
          rw [← mul_assoc]
          apply mul_lt_mul_of_pos_right ?_ npos
          simp only [Nat.mul_sub, Nat.reduceMul]
          rw [two_mul, Nat.add_sub_assoc hh.le]
          simp [hh]
        have hh2: p*n > 2 * (2*p) := by
          rw [mul_comm p n, ← mul_assoc]
          apply mul_lt_mul_of_pos_right ?_ ppos
          linarith only [hn]
        exact hh2.trans hh1
    have hp2: (p-6) * n > 2*p := by
      by_cases hh: p ≤ 12
      · have hh1: (p-6)*n ≥ 1*n := by
          apply mul_le_mul_of_nonneg_right ?_ (by simp)
          exact Nat.le_sub_of_add_le pge
        refine lt_of_lt_of_le ?_ hh1
        simp only [one_mul]
        refine lt_of_lt_of_le ?_ hn
        linarith only [hh]
      · push_neg at hh
        suffices 2 * ((p-6)*n) > 2 * (2*p) by
          simpa only [gt_iff_lt, Nat.ofNat_pos, mul_lt_mul_left] using this
        have hh1: 2 * ((p-6)*n) > p * n := by
          rw [← mul_assoc]
          apply mul_lt_mul_of_pos_right ?_ npos
          simp only [Nat.mul_sub, Nat.reduceMul]
          rw [two_mul, Nat.add_sub_assoc hh.le]
          simp [hh]
        have hh2: p*n > 2 * (2*p) := by
          rw [mul_comm p n, ← mul_assoc]
          apply mul_lt_mul_of_pos_right ?_ ppos
          linarith only [hn]
        exact hh2.trans hh1
    rintro h4
    by_cases hs1: s < 2
    · replace h4: p*n ≤ 5*n + p + p := by
        refine h4.trans ?_
        simp only [add_le_add_iff_left]
        replace hs1: s ≤ 1 := Nat.le_of_lt_succ hs1
        exact mul_le_of_le_one_right' hs1
      replace h4: (p-5)*n ≤ p+p := by
        simp only [Nat.sub_mul, tsub_le_iff_right]
        linarith only [h4]
      absurd h4
      push_neg
      rw [← two_mul]
      exact hp1
    · push_neg at hs1
      replace h4: p*n ≤ 5*n + p + (n+p) := by
        refine h4.trans ?_
        simp [hs hs1]
      absurd h4
      push_neg
      suffices (p-6) * n > 2*p by
        simp only [Nat.sub_mul, gt_iff_lt] at this
        replace: 2*p + 6*n < p*n := Nat.add_lt_of_lt_sub this
        convert this using 1
        ring
      exact hp2

  have cal2 {k i:ℕ} (kle: k ≤ n - 30) (hi: i < 30):
    i + k + 1 ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, true_and]
    have ngt: n > 30 := lt_of_lt_of_le (by norm_num) hn
    clear * - kle hi npos ngt
    omega

  -- for 30 consecutive numbers (here is 0 to 29),
  -- to cover the set using arithmetic sequence with common difference 2,3,5
  -- we can cover at most 22 numbers.
  have cal3 (s: Finset ℕ) (s_def: s = Finset.range 30):
    ∀x1 < 2, ∀x2 < 3, ∀x3 < 5,
    (((s.filter (2 ∣ · - x1))).filter (· ≥ x1) ∪
    ((s.filter (3 ∣ · - x2))).filter (· ≥ x2) ∪
    ((s.filter (5 ∣ · - x3 )).filter (· ≥ x3)) ).card ≤ 22 := by
    rw [s_def]
    clear * -
    native_decide

  have cal4 {d': ℚ} {i j: ℕ} (hi: i ∈ Finset.Icc 1 n) (hd': d' ≠ 0)
    (hj: j ∈ Finset.Icc 1 n) (hlt: d' * (↑j - 1) < d' * (↑i - 1)):
    |d'| ≤ d' * (↑i - 1) - d' * (↑j - 1) := by
    rcases hd'.lt_or_lt with hdd | hdd
    · simp only [hdd, mul_lt_mul_left_of_neg, sub_lt_sub_iff_right,
      Nat.cast_lt, sub_add_cancel, mul_le_mul_left_of_neg, tsub_le_iff_right] at hlt ⊢
      rw [abs_of_neg hdd]
      simp only [neg_le_sub_iff_le_add, ← mul_add_one,
      sub_add_cancel, hdd, mul_le_mul_left_of_neg]
      have: (j-1:ℚ) = ↑(j-1:ℕ) := by
        simp only [Finset.mem_Icc] at hj
        rw [Nat.cast_sub hj.left, Nat.cast_one]
      simp only [this, Nat.cast_le, ge_iff_le]
      exact Nat.le_sub_one_of_lt hlt
    · simp only [hdd, mul_lt_mul_left, sub_lt_sub_iff_right,
      Nat.cast_lt, sub_add_cancel, mul_le_mul_left] at hlt ⊢
      simp only [Finset.mem_Icc] at hi
      rw [abs_of_pos hdd]
      suffices d' * (j-1+1) ≤ d' * (i-1) by
        linarith only [this]
      have: (i-1:ℚ) = ↑(i-1:ℕ) := by
        simp [Nat.cast_sub hi.left]
      simp only [sub_add_cancel, this, hdd,
      mul_le_mul_left, Nat.cast_le, ge_iff_le]
      exact Nat.le_sub_one_of_lt hlt

  have cal5 {s d: ℕ} {c:ℤ} {d':ℚ} (hd': d' ≠ 0) (dpos: 0 < d)
    (hd: d' = c/d) (cnz: c ≠ 0) (hs: s ≥ n - n/2)
    (h1: |d'| * (s - 1) ≤ 10):
    d ≥ (n-2: ℚ) / 20 := by
    have: (0:ℚ) < s - 1 := by
      simp only [sub_pos, Nat.one_lt_cast]
      refine lt_of_lt_of_le ?_ hs
      clear * - hn
      omega
    have h1: |d'| ≤ 10 / (s - 1) := by
      exact (le_div_iff₀ this).mpr h1
    have h2: 1/d ≤ |d'| := by
      rw [hd, abs_div, Nat.abs_cast,
      div_le_div_iff_of_pos_right (by simp [dpos])]
      suffices 0 < |c| by norm_cast
      simp [cnz]
    replace h2 := h2.trans h1
    rw [one_div_le (by simp [dpos]) (by positivity)] at h2
    simp only [one_div, inv_div] at h2
    refine le_trans ?_ h2
    cancel_denoms
    have h3: 1 ≤ s := by
      simp only [sub_pos, Nat.one_lt_cast] at this
      exact this.le
    replace: s - (1:ℚ) = ↑(s - 1) := by
      rw [Nat.cast_sub h3, Nat.cast_one]
    rw [this]
    norm_cast
    rw [← Nat.mul_add_one, Nat.sub_add_cancel h3]
    replace: 2 * s ≥ 2 * n - 2 * (n/2) := by
      rw [← Nat.mul_sub]
      simp only [ge_iff_le, Nat.ofNat_pos, mul_le_mul_left, hs]
    refine le_trans ?_ this
    refine Nat.le_sub_of_add_le ?_
    nth_rw 2 [two_mul]
    simp only [add_le_add_iff_left]
    exact Nat.mul_div_le n 2

  have cal6 {k ii:ℕ} (hk: k < 30) (hii: ii ∈ Finset.range (n/30)):
    k + 30*ii + 1 ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc, le_add_iff_nonneg_left,
    zero_le, true_and]
    rw [show k+30*ii+1 = (k+1) + 30*ii by ring]
    simp only [Finset.mem_range] at hii
    change k+1 ≤ 30 at hk
    have nge30: n ≥ 30 := by linarith only [hn]
    suffices 30*ii ≤ n - 30 by
      replace: 30*ii + 30 ≤ n := Nat.add_le_of_le_sub nge30 this
      linarith only [hk, this]
    suffices 30 * (ii+1) ≤ n by
      rw [Nat.mul_add_one] at this
      exact Nat.le_sub_of_add_le this
    change ii+1 ≤ n/30 at hii
    suffices 30 * (n/30) ≤ n by
      refine le_trans ?_ this
      exact Nat.mul_le_mul_left 30 hii
    exact Nat.mul_div_le n 30

  -- back to the problem.
  -- suppose common difference is d'.
  rcases harprog with ⟨d', harprog⟩
  -- if d = 0, done.
  by_cases hd': d' = 0
  · use (a 1 / b 1: ℚ)
    simp only [hd', zero_mul, add_zero, and_imp] at harprog
    exact harprog
  -- else, we may suppose d' = c/d with c,d coprime.
  obtain ⟨c, d, dpos, co_cd, hd, cnz⟩: ∃ (c:ℤ), ∃ (d: ℕ), 0 < d ∧
    Nat.Coprime c.natAbs d ∧ d' = c/d ∧ c ≠ 0 := by
    use d'.num, d'.den, (Rat.den_pos d'),
      (d'.reduced), ((Rat.num_div_den d')).symm
    exact (fun hh => hh |> Rat.zero_of_num_zero |> hd')

  -- we say index i is p-wrong, if v_p (bi) < v_p (d)
  let p_wrong: ℕ → ℕ → Prop := fun i p =>
    padicValNat p (b i) < padicValNat p d
  have p_wrong_def (i p: ℕ): p_wrong i p =
    (padicValNat p (b i) < padicValNat p d) := rfl

  -- to reach the goal, it suffices to show common difference d ≠ 0 is impossible.
  -- we will prove four big claims, and use these four claims, derive a contradiction.

  -- first claim: for any prime p, all p-wrong indices are congruent modulo p.
  have hc1 {p:ℕ} (pp: Nat.Prime p):
    ∀ i ∈ Finset.Icc 1 n, ∀j ∈ Finset.Icc 1 n,
    p_wrong i p → p_wrong j p → i ≡ j [MOD p] := by
    have: Fact (Nat.Prime p) := by exact { out := pp }
    intro i i_range j j_range hi hj
    rw [p_wrong_def] at hi hj
    have h1: (a i / b i: ℚ) - (a j / b j) = (i - j) * c/d := by
      rw [harprog i i_range, harprog j j_range, hd]
      ring
    have p_dvd_d: p ∣ d := by
      refine dvd_of_one_le_padicValNat ?_
      exact Nat.zero_lt_of_lt hi
    have vp_c_zero: padicValInt p c = 0 := by
      delta padicValInt
      refine padicValNat.eq_zero_of_not_dvd ?_
      by_contra!
      absurd co_cd
      rw [Nat.Prime.not_coprime_iff_dvd]
      exact ⟨p, pp, this, p_dvd_d⟩
    by_contra! hij
    have h2: padicValRat p ((a i / b i: ℚ) - (a j / b j)) =
      - padicValNat p d := by
      have hh1: (i:ℚ) - j ≠ 0 := by
        rintro heq
        replace heq: (i:ℚ) = j := by linarith only [heq]
        norm_cast at heq
        rw [heq] at hij
        apply hij rfl
      have hh2: (c:ℚ)/d ≠ 0 := by positivity
      rw [h1, mul_div_assoc, padicValRat.mul hh1 hh2,
      padicValRat.div (by simp [cnz]) (by simp [dpos.ne'])]
      have hh3: padicValRat p (i-j:ℚ) = 0 := by
        have: (i-j:ℚ) = ↑(i-j:ℤ) := by simp
        rw [this, padicValRat.of_int]
        simp only [Int.natCast_eq_zero]
        refine padicValInt.eq_zero_of_not_dvd ?_
        exact fun hdvd =>
          hij <| Nat.ModEq.symm <| Nat.modEq_of_dvd <| hdvd
      have hh4: padicValRat p c = 0 := by
        simp [padicValRat.of_int, vp_c_zero]
      simp [hh3, hh4]
    have h3: padicValRat p ((a i / b i: ℚ) - (a j / b j)) ≥
      min (padicValRat p (a i / b i: ℚ)) (padicValRat p (-(a j / b j:ℚ)) ) := by
      rw [sub_eq_add_neg]
      apply padicValRat.min_le_padicValRat_add ?_
      rw [harprog i i_range, harprog j j_range]
      ring_nf
      have inej: i ≠ j := (fun hh => hij
        (congrFun (congrArg HMod.hMod hh) p))
      replace inej: (i - j: ℚ) ≠ 0 := by
        qify at inej
        exact sub_ne_zero_of_ne inej
      simp [← mul_sub, hd', inej]
    rw [padicValRat.neg, h2] at h3
    absurd h3
    push_neg
    apply lt_min ?_ ?_
    all_goals
      have hh1 := apos i i_range
      have hh1' := apos j j_range
      have hh2 := bpos i i_range
      have hh2' := bpos j j_range
      rw [padicValRat.div (by positivity) (by positivity)]
      simp only [padicValRat.of_nat, neg_lt_sub_iff_lt_add]
      norm_cast
      exact Nat.lt_add_right _ (by assumption)


  -- second claim: d has no prime divisors ≥ 5
  have hc2 {p:ℕ} (pp: Nat.Prime p) (pdvd: p ∣ d):
    p ≤ 5 := by
    -- suppose on the contrary, p ≥ 7
    by_contra! pge
    replace pge: p ≥ 7 := by
      suffices p ≠ 6 by omega
      rintro peq
      norm_num [peq] at pp
    -- each two p-wrong index congruent modulo p, so they have gap ≥ p,
    -- so at most ceil (n/p) p-wrong indices.
    set s1 := Finset.filter (p_wrong · p) (Finset.Icc 1 n) with s1_def
    have h1 (h: s1.card ≥ 2):
      p * s1.card ≤ n + p := by
      have hub: ∀ i ∈ s1, i ≤ n := by
        suffices s1 ⊆ Finset.Icc 1 n by
          intro i hi
          specialize this hi
          simp only [Finset.mem_Icc] at this
          exact this.right
        rw [s1_def]
        apply Finset.filter_subset
      have hp: ∀ i ∈ s1, ∀ j ∈ s1, i > j → i - j ≥ p := by
        intro i hi j hj hij
        simp only [s1_def, Finset.mem_filter] at hi hj
        specialize hc1 pp i hi.left j hj.left hi.right hj.right
        symm at hc1
        rw [Nat.modEq_iff_dvd' hij.le] at hc1
        exact Nat.le_of_dvd (Nat.zero_lt_sub_of_lt hij) hc1
      replace h := l_dist_mul_card_le_upper_bound_nat hub hp
      simp only [Nat.mul_sub_one, tsub_le_iff_right] at h
      exact h
    -- not p-wrong are divided by p.
    have h2 (i:ℕ) (hi: i ∈ Finset.Icc 1 n):
      ¬ p_wrong i p → p ∣ b i := by
      have: Fact (Nat.Prime p) := by exact { out := pp }
      simp only [p_wrong_def, not_lt]
      intro hh
      refine dvd_of_one_le_padicValNat ?_
      apply le_trans ?_ hh
      refine Nat.one_le_iff_ne_zero.mpr ?_
      refine (dvd_iff_padicValNat_ne_zero dpos.ne').mp pdvd
    set s2 := Finset.filter (p ∣ b · ) (Finset.Icc 1 n) with s2_def
    replace h2: s2.card ≥ n - s1.card := by
      have hh1: Finset.Icc 1 n =
        s1 ∪ (Finset.filter (¬ p_wrong · p) (Finset.Icc 1 n)) := by
        rw [s1_def, Finset.filter_union_filter_neg_eq]
      have hh2: Finset.filter (¬ p_wrong · p) (Finset.Icc 1 n) ⊆
        s2 := by
        intro i
        simp only [Finset.mem_filter, and_imp, s2_def]
        intro hi hh
        exact ⟨hi, h2 i hi hh⟩
      have hh3: (Finset.filter (¬ p_wrong · p) (Finset.Icc 1 n)).card ≥ n - s1.card := by
        simp only [ge_iff_le, tsub_le_iff_right]
        nth_rw 1 [show n = (Finset.Icc 1 n).card by simp, hh1, add_comm _ s1.card]
        apply Finset.card_union_le
      replace hh2 := Finset.card_le_card hh2
      exact hh3.trans hh2
    -- and gap for those bi with not p-wrong indices ≥ p,
    -- they add up to 5n ≥ p (s2.card) ≥ p (n - s1.card) ≥ (p-1)n, contradiction.
    have h3: (Finset.image (fun i => b i) s2).card = s2.card := by
      rw [s2_def, Finset.card_image_of_injOn]
      intro i hi j hj
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi hj
      simp only
      apply b_distinct i hi.left j hj.left
    have h4: p * (s2.card - 1) ≤ 5*n := by
      rw [← h3]
      have hub: ∀x ∈ Finset.image (fun i => b i) s2, x ≤ 5*n := by
        simp only [s2_def, Finset.mem_image, Finset.mem_filter,
        forall_exists_index, and_imp]
        rintro _ i hi _ rfl
        apply ble5n i hi
      have hp: ∀x ∈ Finset.image (fun i => b i) s2,
        ∀y ∈ Finset.image (fun i => b i) s2, x > y → x - y ≥ p := by
        simp only [s2_def, Finset.mem_image, Finset.mem_filter,
        forall_exists_index, and_imp]
        rintro _ i hi hhi rfl _ j hj hhj rfl hlt
        apply Nat.le_of_dvd (Nat.zero_lt_sub_of_lt hlt) ?_
        clear * - hhi hhj
        exact Nat.dvd_sub' hhi hhj
      apply l_dist_mul_card_le_upper_bound_nat hub hp
    replace h4: p * s2.card ≤ 5*n + p := by
      simp only [Nat.mul_sub_one, tsub_le_iff_right] at h4
      exact h4
    replace h4: p*n - p*s1.card ≤ 5*n + p := by
      refine le_trans ?_ h4
      rw [← Nat.mul_sub]
      exact Nat.mul_le_mul_left p h2
    simp only [tsub_le_iff_right] at h4
    exact cal1 pge h1 h4


  -- third claim: for every 0 ≤ k ≤ n-30, among b_{k+1},...,b_{k+30},
  -- at least 8 of them are divisible by p.
  have hc3 {k:ℕ} (kle: k ≤ n - 30):
    (Finset.filter (d ∣ · )
      (Finset.image (fun i => b (i+k+1)) (Finset.range 30))).card ≥ 8 := by
    set f: ℕ → ℕ := fun i => b (i+k+1) with f_def
    set s: Finset ℕ := Finset.range 30 with s_def
    have h1: s.image f =
      (s.image f).filter (d ∣ · ) ∪ (s.image f).filter (¬ d ∣ · ) := by
      rw [Finset.filter_union_filter_neg_eq]
    have finj: Set.InjOn f ↑s := by
      intro i hi j hj heq
      simp only [s_def, Finset.coe_range, Set.mem_Iio] at hi hj
      simp [f_def] at heq
      suffices i+k+1 = j+k+1 by
        simpa only [Nat.add_right_cancel_iff] using this
      apply b_distinct _ (cal2 kle hi) _ (cal2 kle hj) heq
    suffices ((s.image f).filter (¬ d ∣ · )).card ≤ 22 by
      have hh: (s.image f).card = 30 := by
        rw [Finset.card_image_of_injOn finj]
        simp [s_def]
      replace h1: ((s.image f).filter (d ∣ · )).card +
        ((s.image f).filter (¬ d ∣ · )).card ≥ 30 := by
        rw [← hh, ge_iff_le]
        nth_rw 1 [h1]
        apply Finset.card_union_le
      have h2: ((s.image f).filter (d ∣ · )).card ≥ 30 -
        ((s.image f).filter (¬ d ∣ · )).card := by
        simp [h1]
      refine le_trans ?_ h2
      generalize ((s.image f).filter (¬ d ∣ · )).card = kk at this ⊢
      clear * - this
      omega
    -- if d not divide some bi, then i must be 2-wrong, 3-wrong or 5-wrong
    set g: ℕ → ℕ := fun i => i + k + 1 with g_def
    set t: Finset ℕ := s.image g with t_def
    have mem_of_mem_t {i:ℕ} (hi: i ∈ t): i ∈ Finset.Icc 1 n := by
      simp only [t_def, g_def, Finset.mem_image] at hi
      rcases hi with ⟨j, j_mem, ieq⟩
      rw [← ieq]
      simp only [s_def, Finset.mem_range] at j_mem
      apply cal2 kle j_mem
    have h2: (s.image f).filter (¬ d ∣ · ) ⊆
      (t.filter (p_wrong · 2)).image b ∪ (t.filter (p_wrong · 3)).image b
      ∪ (t.filter (p_wrong · 5)).image b := by
      intro x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.union_assoc,
      Finset.mem_union, and_imp, forall_exists_index]
      intro i hi xeq not_dvd
      simp only [f_def] at xeq
      have hh: i+k+1 ∈ t := by
        simp [t_def, g_def, hi]
      have xpos: 0 < x := by
        rw [← xeq]
        simp only [s_def, Finset.mem_range] at hi
        apply bpos _ (cal2 kle hi)
      rw [← Nat.factorization_prime_le_iff_dvd dpos.ne' xpos.ne'] at not_dvd
      simp only [p_wrong_def]
      by_contra!
      rw [← xeq] at not_dvd this
      absurd not_dvd
      intro p pp
      simp only [Nat.factorization_def _ pp]
      by_cases hp: p ∣ d
      · specialize hc2 pp hp
        have peq: p = 2 ∨ p = 3 ∨ p = 5 := by
          revert pp
          clear * - hc2
          native_decide +revert
        rcases peq with peq | peq | peq
        all_goals
          simp [peq, this]
          by_contra! pv_lt
        · replace := this.left (i+k+1) ⟨hh, pv_lt⟩
          simp at this
        · replace := this.right.left (i+k+1) ⟨hh, pv_lt⟩
          simp at this
        · replace := this.right.right (i+k+1) ⟨hh, pv_lt⟩
          simp at this
      · suffices padicValNat p d = 0 by simp [this]
        exact padicValNat.eq_zero_of_not_dvd hp
    simp only [← Finset.image_union, ← Finset.filter_or,
    t_def, Finset.filter_image] at h2
    replace h2 := Finset.card_le_card h2
    -- if g(i), g(j) are p-wrong, then i ≡ j mod p
    have h3 (p:ℕ) (pp: Nat.Prime p):
      ∀i ∈ s.filter (fun x => p_wrong (g x) p),
      ∀j ∈ s.filter (fun x => p_wrong (g x) p),
      i ≡ j [MOD p] := by
      intro i hi j hj
      simp only [g_def, s_def,
      Finset.mem_filter, Finset.mem_range] at hi hj
      specialize hc1 pp (i+k+1) (cal2 kle hi.left)
        (j+k+1) (cal2 kle hj.left) hi.right hj.right
      simp only [add_assoc _ k 1] at hc1
      apply Nat.ModEq.add_right_cancel' _ hc1
    -- so we claim the set can be covered by arithmetic sequence.
    simp only [Finset.filter_or] at h2
    have h31 := l_ar_prog_cover 2 (by norm_num) s (h3 2 (by norm_num))
    have h32 := l_ar_prog_cover 3 (by norm_num) s (h3 3 (by norm_num))
    have h33 := l_ar_prog_cover 5 (by norm_num) s (h3 5 (by norm_num))
    rcases h31 with ⟨x1, x1lt, h31⟩
    rcases h32 with ⟨x2, x2lt, h32⟩
    rcases h33 with ⟨x3, x3lt, h33⟩
    replace h3 := l_finset_union_subset_union_3 h31 h32 h33
    specialize cal3 s rfl x1 x1lt x2 x2lt x3 x3lt
    replace h3 := (Finset.card_le_card h3).trans cal3
    simp only [← Finset.filter_or] at h3
    simp only [Finset.filter_image, ge_iff_le]
    refine h2.trans (le_trans ?_ h3)
    simp only [Finset.union_assoc, Finset.filter_or]
    rw [Finset.card_image_of_injOn, Finset.card_image_of_injOn]
    · intro i _ j _
      simp [g_def]
    · intro x1 hx1 x2 hx2
      simp [s_def] at hx1 hx2
      rcases hx1 with ⟨i1, i1lt, hi1⟩
      rcases hx2 with ⟨i2, i2lt, hi2⟩
      replace i1lt: i1 < 30 := by
        clear * - i1lt
        tauto
      replace i2lt: i2 < 30 := by
        clear * - i2lt
        tauto
      simp only [g_def] at hi1 hi2
      rw [← hi1, ← hi2]
      apply b_distinct _ (cal2 kle i1lt) _ (cal2 kle i2lt)


  -- fourth claim: d ≥ n-2 / 20
  have hc4: d ≥ (n-2: ℚ) / 20 := by
    -- remove all fractions with b_i < n/2 from whole sequence.
    set s: Finset ℚ := Finset.image (fun i => (a i / b i: ℚ))
      (Finset.Icc 1 n) with s_def
    set s1: Finset ℚ := Finset.image (fun i => (a i / b i: ℚ))
      (Finset.filter (b · < (n/2:ℚ)) (Finset.Icc 1 n)) with s1_def
    set s2: Finset ℚ := Finset.image (fun i => (a i / b i: ℚ))
      (Finset.filter (¬ b · < (n/2:ℚ)) (Finset.Icc 1 n)) with s2_def
    have seq: s = s1 ∪ s2 := by
      rw [s1_def, s2_def, s_def, ← Finset.image_union,
      Finset.filter_union_filter_neg_eq]
    have scard: s.card = n := by
      rw [s_def, Finset.card_image_of_injOn]
      simp only [Nat.card_Icc, add_tsub_cancel_right]
      intro i hi j hj
      norm_cast at hi hj
      simp [harprog i hi, harprog j hj, hd']
    -- bi are distinct, so at most n/2 bi < n/2.
    have s1card: s1.card ≤ n/2 := by
      have h1: s1.card = (Finset.filter (b · < (n/2:ℚ)) (Finset.Icc 1 n)).card := by
        rw [s1_def, Finset.card_image_of_injOn]
        intro i hi j hj
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi hj
        simp [harprog i hi.left, harprog j hj.left, hd']
      have h2: ((Finset.Icc 1 n).filter (b · < (n/2:ℚ))).card =
        (Finset.image (fun i => b i)
          ((Finset.Icc 1 n).filter (b · < (n/2:ℚ)))).card := by
        rw [Finset.card_image_of_injOn]
        simp only [Finset.coe_filter]
        intro i hi j hj
        simp only [Set.mem_setOf_eq] at hi hj
        simp only
        apply b_distinct i hi.left j hj.left
      have h3: Finset.image (fun i => b i)
        ((Finset.Icc 1 n).filter (b · < (n/2:ℚ))) ⊆
        Finset.Icc 1 (n/2) := by
        intro _
        simp only [Finset.mem_image, Finset.mem_filter,
        forall_exists_index, and_imp]
        rintro i hi hh rfl
        simp only [Finset.mem_Icc]
        constructor
        · change 0 < b i
          apply bpos i hi
        · rcases (Nat.even_or_odd' n) with ⟨m, hm⟩
          rcases hm with hm | hm
          · simp only [hm, Nat.cast_mul, Nat.cast_ofNat, ne_eq,
            OfNat.ofNat_ne_zero, not_false_eq_true,
            mul_div_cancel_left₀, Nat.cast_lt] at hh ⊢
            exact hh.le
          · have hm': 2*m+1 < 2*(m+1) := by linarith only
            replace hh: b i < m+1 := by
              qify
              apply lt_trans hh ?_
              rw [← hm] at hm'
              qify at hm'
              linarith only [hm']
            replace hh: b i ≤ m := Nat.le_of_lt_succ hh
            apply hh.trans ?_
            nth_rw 1 [show m = (2*m)/2 by simp, hm]
            apply Nat.div_le_div_right (by simp)
      replace h3 := Finset.card_le_card h3
      rw [← h2, ← h1] at h3
      simp only [Nat.card_Icc, add_tsub_cancel_right] at h3
      exact h3
    -- so #s2 ≥ n - n/2
    have s2card: s2.card ≥ n - n/2 := by
      suffices s2.card ≥ n - s1.card by
        apply le_trans ?_ this
        exact Nat.sub_le_sub_left s1card n
      simp only [ge_iff_le, tsub_le_iff_right, ← scard]
      rw [add_comm s2.card s1.card, seq]
      exact Finset.card_union_le s1 s2
    -- and elements in s2 cannot exceed 10
    have hub: ∀ x ∈ s2, x ≤ 10 := by
      simp only [s2_def, Finset.mem_image, Finset.mem_filter,
      forall_exists_index, and_imp]
      rintro _ i hi bge rfl
      push_neg at bge
      have hh1: (a i / b i: ℚ) ≤ a i / (n/2:ℚ) := by
        rw [div_le_div_iff_of_pos_left]
        all_goals norm_cast
        · apply apos i hi
        · apply bpos i hi
        · simp [npos]
      have hh2: (a i: ℚ) / (n/2) ≤ (5*n:ℚ) / (n/2:ℚ) := by
        specialize ale5n i hi
        rw [div_le_div_iff_of_pos_right]
        all_goals norm_cast
        simp [npos]
      apply (hh1.trans hh2).trans (le_of_eq ?_)
      field_simp
      ring
    -- and it's subset of an arithmetic progression with common difference d'.
    have hhd: ∀x ∈ s2, ∀y ∈ s2, x > y → x - y ≥ |d'| := by
      simp only [s2_def, not_lt, Finset.mem_image, Finset.mem_filter,
      forall_exists_index, and_imp]
      rintro _ i hi _ rfl _ j hj _ rfl hlt
      rw [harprog i hi, harprog j hj] at hlt ⊢
      simp only [gt_iff_lt, add_lt_add_iff_left,
      add_sub_add_left_eq_sub, ge_iff_le] at hlt ⊢
      push_neg at hd'
      exact cal4 hi hd' hj hlt
    -- interval (0, 10] contain at least n/2 elements, each has distance ≥ d'.
    -- therefore d' (n - n/2 - 1) ≤ 10
    have h1: |d'| * (s2.card - 1) ≤ 10 := by
      apply l_dist_mul_card_le_upper_bound_rat hub ?_
        (by norm_num) ?_ hhd
      · simp only [s2_def, not_lt, Finset.mem_image,
        Finset.mem_filter, forall_exists_index, and_imp]
        rintro _ i hi _ rfl
        apply div_nonneg <;> positivity
      · simp [hd']
    apply cal5 hd' dpos hd cnz s2card h1


  -- using above four claims, we can reach a contradiction.
  -- consider set of all bi. each b ≤ 5n, so this set has an upper bound of 5n.
  set s: Finset ℕ := Finset.image (fun i => b i) (Finset.Icc 1 n) with s_def
  have snz: s.Nonempty := by
    rw [s_def]
    have: 1 ≤ n := by omega
    simp [this]
  -- cut [1, n] into several intervals, each interval has length 30.
  -- there are floor (n/30) such intervals in total.
  -- and by claim 3, from each such interval, at least 8 elements are divided by d.
  -- so at least 8 ⌊n/30⌋ b_i are divided by d.
  set t: ℕ → Finset ℕ := fun k =>
    (Finset.image (fun i => b (i+30*k+1)) (Finset.range 30)) with t_def
  have h2: (Finset.filter (d ∣ · ) s).card ≥ 8 * (n/30) := by
    have hh1: (Finset.range (n/30)).biUnion t ⊆ s := by
      simp only [t_def, Finset.biUnion_subset_iff_forall_subset]
      intro j jlt
      rintro _
      simp only [Finset.mem_image, Finset.mem_range, forall_exists_index, and_imp]
      rintro i ilt rfl
      simp only [s_def, Finset.mem_image]
      use (i + 30*j + 1)
      specialize cal6 ilt jlt
      simp only [cal6, and_self]
    replace hh1: (s.filter (d ∣ · )).card ≥
      (((Finset.range (n/30)).biUnion t) |> Finset.filter (d ∣ · )).card := by
      apply Finset.card_le_card ?_
      apply Finset.filter_subset_filter _ hh1
    have hh2: ∀ i ∈ Finset.range (n/30), ∀ j ∈ Finset.range (n/30),
      i ≠ j → Disjoint (t i) (t j) := by
      intro i hi j hj inej
      simp only [t_def]
      by_contra!
      rw [Finset.not_disjoint_iff] at this
      rcases this with ⟨x, hx⟩
      simp only [Finset.mem_image, Finset.mem_range] at hx
      rcases hx with ⟨ ⟨k1, hk1⟩, ⟨k2, hk2⟩ ⟩
      have: k1 + 30*i + 1 = k2 + 30*j + 1 := by
        apply b_distinct _ ?_ _ ?_ ?_
        · apply cal6 hk1.left hi
        · apply cal6 hk2.left hj
        · rw [hk1.right, hk2.right]
      rcases inej.lt_or_lt with hij | hij
      all_goals
        absurd this
        push_neg
      · apply ne_of_lt
        simp only [add_lt_add_iff_right]
        change i+1 ≤ j at hij
        linarith only [hk1.left, hk2.left, hij]
      · apply ne_of_gt
        simp only [add_lt_add_iff_right]
        change j+1 ≤ i at hij
        linarith only [hk1.left, hk2.left, hij]
    rw [Finset.filter_biUnion, Finset.card_biUnion] at hh1
    · apply le_trans ?_ hh1
      suffices ∑ i ∈ Finset.range (n/30), 8 ≤
        ∑ i ∈ Finset.range (n/30),  ((t i).filter (d ∣ · )).card by
        rw [mul_comm 8 _]
        convert this using 1
        simp
      apply Finset.sum_le_sum ?_
      intro i hi
      simp only [t_def]
      apply hc3 ?_
      refine Nat.le_sub_of_add_le ?_
      simp only [Finset.mem_range] at hi
      rw [← Nat.mul_add_one]
      change i+1 ≤ n/30 at hi
      suffices 30 * (n/30) ≤ n by
        apply le_trans ?_ this
        exact Nat.mul_le_mul_left 30 hi
      exact Nat.mul_div_le n 30
    · intro i hi j hj inej
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      specialize hh2 i (by simp [hi]) j (by simp [hj]) inej
      clear * - hh2
      dsimp [Function.onFun]
      have: Disjoint (t i) ((t j).filter (d ∣ · )) := by
        apply Finset.disjoint_of_subset_right ?_ hh2
        apply Finset.filter_subset
      apply Finset.disjoint_of_subset_left ?_ this
      apply Finset.filter_subset
  -- that set has upper bound 5n, and each distance ≥ d,
  -- therefore 8 (n/30) d ≤ 5n
  have h3: d * (8 * (n/30) - 1) ≤ 5*n := by
    suffices d * ((Finset.filter (d ∣ · ) s).card - 1) ≤ 5*n by
      refine le_trans ?_ this
      simp only [dpos, mul_le_mul_left]
      exact Nat.sub_le_sub_right h2 1
    have hub: ∀ x ∈ s.filter (d ∣ · ), x ≤ 5*n := by
      intro _
      simp only [s_def, Finset.mem_filter, Finset.mem_image,
      and_imp, forall_exists_index]
      rintro i hi rfl _
      apply ble5n i hi
    have hd: ∀ x ∈ s.filter (d ∣ · ), ∀y ∈ s.filter (d ∣ · ),
      x > y → x - y ≥ d := by
      simp only [s_def, Finset.mem_filter, Finset.mem_image,
      gt_iff_lt, ge_iff_le, and_imp, forall_exists_index]
      rintro _ i hi rfl hh1 _ j hj rfl hh2 hlt
      apply Nat.le_of_dvd (Nat.zero_lt_sub_of_lt hlt)
      exact Nat.dvd_sub' hh1 hh2
    apply l_dist_mul_card_le_upper_bound_nat hub hd
  have h4: (8 * ((n/30:ℚ)-1)-1:ℚ) * ((n-2)/20) ≤ 5*n := by
    qify at h3
    apply le_trans ?_ h3
    have hh: n/30 ≥ 1 := by
      suffices n ≥ 30 by
        exact (Nat.one_le_div_iff (by norm_num)).mpr this
      apply le_trans (by norm_num) hn
    have: 1 ≤ 8 * (n/30) := by
      linarith only [hh]
    rw [Nat.cast_sub this]
    push_cast
    rw [mul_comm (d:ℚ) _]
    have hh1: 0 < (n-2:ℚ)/20 := by
      apply div_pos ?_ (by norm_num)
      simp only [sub_pos, Nat.ofNat_lt_cast]
      linarith only [hn]
    suffices h:(8 * ((n/30:ℚ)-1)-1:ℚ) ≤ 8 * ↑(n/30:ℕ) - 1 by
      replace: (8 * ((n/30:ℚ)-1)-1:ℚ) * ((n-2)/20) ≤
        (8 * ↑(n/30:ℕ) - 1) * ((n-2)/20) := by
        simp only [hh1, mul_le_mul_right, h]
      apply le_trans this ?_
      apply (mul_le_mul_iff_of_pos_left ?_).mpr hc4
      simp only [sub_pos]
      norm_cast
      linarith only [hh]
    simp only [tsub_le_iff_right, sub_add_cancel,
    Nat.ofNat_pos, mul_le_mul_left]
    suffices (n/30:ℚ) * 30 ≤ (↑(n/30:ℕ)+1) * 30 by
      apply (mul_le_mul_iff_of_pos_right (by norm_num)).mp this
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, IsUnit.div_mul_cancel, add_one_mul]
    norm_cast
    nth_rw 1 [← Nat.div_add_mod' n 30]
    simp only [add_le_add_iff_left]
    apply le_of_lt <| Nat.mod_lt _ <| (by norm_num)

  -- thus we reach a contradiction
  absurd h4
  push_neg
  -- some calculations
  suffices 4*n^2 - 1643*n + (270:ℚ) > 0 by
    linarith only [this]
  suffices n*(4*n - 1643: ℚ) > 0 by
    linarith only [this]
  apply mul_pos (by simp [npos]) ?_
  simp only [sub_pos]
  norm_cast
  linarith only [hn]