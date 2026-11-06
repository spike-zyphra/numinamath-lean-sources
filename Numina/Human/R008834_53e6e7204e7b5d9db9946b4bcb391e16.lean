import Mathlib

/- Let $a_{0}$ be an arbitrary positive integer. Consider the infinite sequence $\left(a_{n}\right)_{n \geq 1}$,
defined inductively as follows: given $a_{0}, a_{1}, \ldots, a_{n-1}$
define the term $a_{n}$ as the smallest positive integer such that $a_{0}+a_{1}+\ldots+a_{n}$ is divisible by $n$.
Prove that there exists a positive integer $M$ such that $a_{n+1}=a_{n}$ for all $n \geq M$. -/
theorem number_theory_605821{a: ℕ → ℕ}(a0pos: 0 < a 0)
  (hasucc: ∀m, 0 < m →
    IsLeast {am:ℕ | 0 < am ∧ m ∣ ∑ i ∈ Finset.range m, a i + am} (a m) ):
  ∃ M, ∀n, n ≥ M → a (n+1) = a n := by
  -- define bn = (a0+a1+...+an)/n
  -- by our definition here, 0 appear as denominator of b0.
  -- but through out the proof, we only care about n > 0 parts
  -- so it does not matter what b0 is.
  set b : ℕ → ℕ := fun n =>
    (∑ i ∈ Finset.range (n+1), a i)/n  with b_def
  -- by definition of an, n ∣ a0+a1+...+an, and an is positive.
  have ha{n:ℕ}(hn: 0 < n): 0 < a n ∧  n ∣ ∑ i ∈ Finset.range (n+1), a i := by
    have := hasucc n
    simp only [IsLeast, Set.mem_setOf_eq] at this
    rw [Finset.sum_range_succ]
    exact (this hn).left
  -- therefore sum ai is positive.
  have asumpos(n:ℕ): 0 < ∑ i ∈ Finset.range (n+1), a i := by
    apply Finset.sum_pos
    · intro i _
      by_cases hi: i = 0
      · simp [hi, a0pos]
      · apply (ha ?_).left
        exact Nat.zero_lt_of_ne_zero hi
    · simp
  -- sum ai = n bn
  have nbn_eq_sum_a{n:ℕ}(hn: 0 < n):
    ∑ i ∈ Finset.range (n+1), a i = n * b n := by
    simp only [b_def]
    rw [Nat.mul_div_cancel' (ha hn).right]
  -- then 0 < b n for all n.
  have bpos{n:ℕ}(hn: 0 < n): 0 < b n := by
    have := asumpos n
    rw [nbn_eq_sum_a hn] at this
    exact Nat.pos_of_mul_pos_left this
  -- we claim a_{n+1} ≤ bn
  have h1{n:ℕ}(hn: 0 < n): a (n+1) ≤ b n := by
    have := hasucc (n+1) (by simp)
    simp only [IsLeast, Set.mem_setOf_eq,
    lowerBounds, and_imp] at this
    apply this.right (bpos hn) ?_
    rw [nbn_eq_sum_a hn]
    nth_rw 2 [← one_mul (b n)]
    rw [← Nat.add_mul]
    apply Nat.dvd_mul_right
  -- then b_{n+1} ≤ bn since a_{n+1} ≤ bn
  have b_not_inc{n:ℕ}(hn: 0 < n):
    b (n+1) ≤ b n := by
    have: ∑ i ∈ Finset.range (n+1+1), a i ≤
      (∑ i ∈ Finset.range (n+1), a i) + b n := by
      nth_rw 1 [Finset.sum_range_succ]
      -- a_{n+1} ≤ bn
      simp only [add_le_add_iff_left, h1 hn]
    -- left side is (n+1) b_{n+1}
    nth_rw 1 [nbn_eq_sum_a (by simp)] at this
    -- right side is exactly (n+1)bn
    have rhs: (∑ i ∈ Finset.range (n+1), a i) + b n =
      (n+1) * b n := by
      rw [Nat.add_mul, one_mul, add_left_inj]
      apply nbn_eq_sum_a hn
    rw [rhs] at this
    exact Nat.le_of_mul_le_mul_left this (by simp)
  -- then also we have b_{n+m} ≤ bn
  replace b_not_inc{n m: ℕ}(hn: 0 < n):
    b (n+m) ≤ b n := by
    induction' m with m ih
    · simp
    · rw [← add_assoc]
      apply le_trans ?_ ih
      apply b_not_inc (by linarith [hn])
  -- we claim b is eventually constant.
  -- it is because b is natural number series,
  -- and we cannot build an infinite descending chain on natural number.
  have hb: ∃ T, 0 < T ∧ ∀n, n ≥ T → b (n+1) = b n := by
    by_contra! h
    -- if it's not the case, then bm can reach b1 - x for arbitrarily large x.
    have not_bounded: ∀x:ℕ, ∃ m, 0 < m ∧ b m ≤ (b 1) - x := by
      intro x
      induction' x with x ih
      · use 1; simp
      · rcases ih with ⟨m0, m0pos, hm0⟩
        rcases (h m0 m0pos) with ⟨n0, hge, hn0⟩
        use (n0+1)
        rw [Nat.sub_add_eq]
        refine ⟨(by simp), ?_⟩
        have n0pos: 0 < n0 := lt_of_lt_of_le m0pos hge
        have h2: b (n0+1) < b n0 :=
          lt_of_le_of_ne (b_not_inc n0pos) hn0
        have h3: b n0 ≤ b 1 - x := by
          apply le_trans ?_ hm0
          rw [← add_tsub_cancel_of_le hge]
          apply b_not_inc m0pos
        apply Nat.le_sub_one_of_lt
        apply lt_of_lt_of_le h2 h3
    -- therefore we prove b is not lower bounded.
    -- but natural number ≥ 0, contradiction.
    specialize not_bounded (b 1)
    simp only [tsub_self,
    nonpos_iff_eq_zero] at not_bounded
    rcases not_bounded with ⟨m, mpos, hm⟩
    specialize h m mpos
    rcases h with ⟨n, hn⟩
    have: b (n+1) < 0 := by
      rw [← hm]
      have: b n ≤ b m := by
        rw [← add_tsub_cancel_of_le hn.left]
        apply b_not_inc mpos
      apply lt_of_lt_of_le ?_ this
      apply lt_of_le_of_ne (b_not_inc ?_) hn.right
      linarith [hn.left, mpos]
    simp at this
  -- from b is eventually constant, easy to show a is also eventually constant.
  rcases hb with ⟨T, Tpos, hT⟩
  -- for all n ≥ T, we can prove a_{n+1} = bn
  have hab{n:ℕ}(hn: n ≥ T): a (n+1) = b n := by
    have npos: 0 < n := by linarith [hn, Tpos]
    have n1pos: 0 < n+1 := by simp
    -- given b (n+1) = bn, we have n(n+1) b (n+1) = n (n+1) bn
    have h2: ((n+1) * b (n+1)) * n = (n * b n) * (n+1) := by
      rw [hT n (by linarith [hn])]; ring
    -- n bn = a0+a1+...+an
    rw [← nbn_eq_sum_a npos, ← nbn_eq_sum_a n1pos] at h2
    -- rearrange, n (a_{n+1}) = a0+a1+...+an
    replace h2: n * a (n+1) = ∑ i ∈ Finset.range (n+1), a i := by
      nth_rw 1 [Finset.sum_range_succ] at h2
      rw [Nat.add_mul, Nat.mul_add, mul_one] at h2
      rwa [add_right_inj, mul_comm _ n] at h2
    -- right side is n bn
    rw [nbn_eq_sum_a npos] at h2
    -- therefore a (n+1) = bn
    exact Nat.eq_of_mul_eq_mul_left npos h2
  -- then a_{n+2} = a_{n+1} for all n ≥ T.
  -- or, a_{n+1} = a_n for all n ≥ T+1
  use T+1
  intro n hn
  have nge: 1 ≤ n := by linarith [hn]
  have nge': n-1 ≥ T := by
    exact (Nat.le_sub_one_iff_lt nge).mpr hn
  have hn': n-1+1 ≥ T := by
    linarith [nge']
  have: n = n-1+1 := by simp [nge]
  rw [this, hab nge', hab hn', hT (n-1) nge']