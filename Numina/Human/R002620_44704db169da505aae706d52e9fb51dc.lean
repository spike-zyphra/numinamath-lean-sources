import Mathlib

/- For each real number x, let $\lfloor x \rfloor$ denote the greatest integer that does not exceed x.
   For how many positive integers $n$ is it true that $n<1000$ and that $\lfloor \log_2 n \rfloor$ is a positive even integer? -/
theorem number_theory_96633 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 1000 ∧ 0 < Nat.floor (Real.logb 2 n) ∧ Even (Nat.floor (Real.logb 2 n))} = 340 := by
  -- for integers k, we want $\lfloor \log_2 n \rfloor = 2k$, or $2k \le \log_2 n < 2k+1$
  have (n : ℕ) (h : 0 < n) : (0 < Nat.floor (Real.logb 2 n) ∧ Even (Nat.floor (Real.logb 2 n))) ↔
      ∃ k : ℕ, 0 < k ∧ 2 * k ≤ Real.logb 2 n ∧ Real.logb 2 n < 2 * k + 1 := by
    rw[Even, ← exists_and_left]
    apply exists_congr
    intro k
    -- use floor characterization
    rw[Nat.floor_eq_iff (Real.logb_nonneg (by simp) (by rw[← Order.one_le_iff_pos] at h; simp[h]))]
    simp[two_mul]
    intro two_k_le log_lt
    rw[Nat.floor_pos]
    -- show a bunch of required positivity constraints
    constructor
    · intro log_pos
      have := lt_of_le_of_lt log_pos log_lt
      suffices le_r : 0 < (k : ℝ) by
        rwa[Nat.cast_pos] at le_r
      linarith
    · intro k_pos
      have one_le_k := Nat.one_le_of_lt k_pos
      have one_le_k' : 1 ≤ (k : ℝ) + (k : ℝ) := by
        trans ↑k
        · simp[one_le_k]
        · simp
      apply le_trans one_le_k' two_k_le
  -- equivalently, $2^{2k} \le n < 2^{2k+1}$.
  replace this (n : ℕ) (h : 0 < n) : (0 < Nat.floor (Real.logb 2 n) ∧ Even (Nat.floor (Real.logb 2 n))) ↔
      ∃ k : ℕ, 0 < k ∧ 2^(2 * k) ≤ n ∧ n < 2^(2 * k + 1) := by
    rw[this]
    apply exists_congr
    intro k
    rw[and_congr_right_iff]
    intro kpos
    apply and_congr
    · rw[Real.le_logb_iff_rpow_le]
      · rw[← Nat.cast_two, ← Nat.cast_mul, Real.rpow_natCast, ← Nat.cast_pow, Nat.cast_le]
      · simp
      · simp[h]
    · rw[Real.logb_lt_iff_lt_rpow]
      · rw[← Nat.cast_two, ← Nat.cast_mul, ← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast, ← Nat.cast_pow, Nat.cast_lt]
      · simp
      · simp[h]
    · assumption
  -- Thus $n$ satisfies one of the inequalities $4 \le n < 8, 16 \le n < 32, 64 \le n < 128, 256 \le n < 512$.
  replace this (n : ℕ) (h : 0 < n) (h' : n < 1000) : (0 < Nat.floor (Real.logb 2 n) ∧ Even (Nat.floor (Real.logb 2 n))) ↔
      (4 ≤ n ∧ n < 8) ∨ (16 ≤ n ∧ n < 32) ∨ (64 ≤ n ∧ n < 128) ∨ (256 ≤ n ∧ n < 512) := by
    rw[this n h]
    constructor
    · rintro ⟨k, kpos, pow_k_le, lt_pow_k⟩
      -- since 2^10 = 1024 > 1000, the largest possible k is 4
      have k_le : k < 5 := by
        rw[lt_iff_not_le]
        intro le_k
        have : 10 ≤ 2 * k := by linarith
        have thousand_le : 1024 ≤ 2 ^ (2 * k) := by
          change 2^10 ≤ 2 ^ (2 * k)
          apply Nat.pow_le_pow_right (by simp) this
        have : 1000 < 1024 := by simp
        linarith
      have k_le' : k ∈ Finset.Ioo 0 5 := by simp[k_le, kpos]
      fin_cases k_le'
      -- k = 1
      · left
        exact ⟨pow_k_le, lt_pow_k⟩
      -- k = 2
      · right; left
        exact ⟨pow_k_le, lt_pow_k⟩
      -- k = 3
      · right; right; left
        exact ⟨pow_k_le, lt_pow_k⟩
      -- k = 4
      · right; right; right
        exact ⟨pow_k_le, lt_pow_k⟩
    · rintro (⟨le,lt⟩|⟨le,lt⟩|⟨le,lt⟩|⟨le,lt⟩)
      · exists 1
      · exists 2
      · exists 3
      · exists 4
  -- Hence the set is a union of intervals
  replace this : {n : ℕ | 0 < n ∧ n < 1000 ∧ 0 < Nat.floor (Real.logb 2 n) ∧ Even (Nat.floor (Real.logb 2 n))} =
      Set.Ico 4 8 ∪ Set.Ico 16 32 ∪ Set.Ico 64 128 ∪ Set.Ico 256 512 := by
    ext n
    constructor
    · rintro ⟨npos,nle,hn⟩
      rw[this n npos nle] at hn
      simp only [Set.mem_union, Set.mem_Ico]
      tauto
    · intro hn
      -- all the intervals are contained in (0,1000)
      have bounds : 0 < n ∧ n < 1000 := by
        rcases hn with ((⟨le,lt⟩|⟨le,lt⟩)|⟨le,lt⟩)|⟨le,lt⟩
          <;> exact ⟨lt_of_lt_of_le (by simp) le, lt_trans lt (by simp)⟩
      refine ⟨bounds.1, ⟨bounds.2, ?goal⟩⟩
      rw[this]
      · simp at hn
        tauto
      exact bounds.1
      exact bounds.2
  rw[this]
  -- whose cardinality can be easily determined, as long as we show disjointness.
  rw[Set.ncard_eq_toFinset_card']
  rw[Set.toFinset_union, Set.toFinset_union, Set.toFinset_union]
  rw[Finset.card_union_of_disjoint ?disj1, Finset.card_union_of_disjoint ?disj2, Finset.card_union_of_disjoint ?disj3]
  simp
  -- but due to the inequalities, the sets are all disjoint.
  · rw[Finset.disjoint_left]
    rintro a h1 h2
    simp at h1 h2
    have lt_self := lt_trans h1.2 (lt_of_lt_of_le (by simp) h2.1)
    apply lt_irrefl _ lt_self
  · rw[Finset.disjoint_left]
    rintro a h1 h2
    simp at h1 h2
    rcases h1 with (h1|h1) <;>
    { have lt_self := lt_trans h1.2 (lt_of_lt_of_le (by simp) h2.1)
      apply lt_irrefl _ lt_self }
  · rw[Finset.disjoint_left]
    rintro a h1 h2
    simp at h1 h2
    rcases h1 with (h1|h1|h1) <;>
    { have lt_self := lt_trans h1.2 (lt_of_lt_of_le (by simp) h2.1)
      apply lt_irrefl _ lt_self }