import Mathlib
/- Let $N$ be a positive integer. Let $a_k$ denote the integer closest to $\sqrt{k}$. Calculate the sum $S_N = \sum_{k=1}^{N} \frac{1}{a_k}$. Show that the sum is equal to $M-1 + \frac{N}{M}$, where $M$ is the integer closest to $\sqrt{N}$. -/
theorem number_theory_637810 (a : ℕ → ℤ) (N : ℕ) (hN : N > 0) (ha : ∀ k, a k = round (√k)) : ∑ k in Finset.range N, (1 : ℝ) / a (k + 1) = round (√N) - 1 + N / round (√N) := by
  -- Key lemma: round(√(k+1)) = m if and only if m²-m+1 ≤ k+1 ≤ m²+m
  have h1 : ∀ k : ℕ, ∀ m : ℤ, round √(k + 1) = m ↔ m ^ 2 - m + 1 ≤ k + 1 ∧ k + 1 ≤ m ^ 2 + m:= by
    intro k m
    constructor
    .
      -- Forward direction: if round(√(k+1)) = m, then m²-m+1 ≤ k+1 ≤ m²+m
      intro h
      rw [round_eq _] at h
      apply Int.floor_eq_iff.1 at h
      rcases h with ⟨h1, h2⟩
      -- Show that m ≥ 1
      have hm : m ≥ 1:= by
        by_contra H
        replace H : m ≤ 0:= by linarith
        rify at H
        have g : √(k + 1) ≥ 1:= by
          have g : k + 1 ≥ 1:= by omega
          rify at g
          exact Real.one_le_sqrt.mpr g
        linarith
      -- Transform the inequalities to work with absolute values
      replace h1 : |(m : ℝ) - 1 / 2| ≤ |√(k + 1)|:= by
        rify at hm
        rw [abs_of_nonneg (by linarith)]
        rw [abs_of_nonneg (by positivity)]
        linarith
      replace h2 : |(m : ℝ) + 1 / 2| > |√(k + 1)|:= by
        rify at hm
        rw [abs_of_nonneg (by linarith)]
        rw [abs_of_nonneg (by positivity)]
        linarith
      -- Square both sides to get quadratic inequalities
      replace h1:= sq_le_sq.mpr h1
      replace h2:= sq_lt_sq.mpr h2
      field_simp at h1 h2
      ring_nf at h1 h2
      rify at hm
      constructor
      .
        -- Prove m²-m+1 ≤ k+1
        by_contra H
        replace H : m ^ 2 - m ≥ k + 1:= by linarith
        rify at H
        linarith
      .
        -- Prove k+1 ≤ m²+m
        by_contra H
        replace H : m ^ 2 + m + 1 ≤ k + 1:= by linarith
        rify at H
        linarith
    .
      -- Reverse direction: if m²-m+1 ≤ k+1 ≤ m²+m, then round(√(k+1)) = m
      intro h
      rcases h with ⟨h1, h2⟩
      -- Show that m ≥ 1
      have hm : m ≥ 1:= by
        by_contra H
        replace H : m ≤ 0:= by linarith
        linarith
      rify at h1 h2
      -- Transform to square root inequalities
      replace h1 : ((m : ℝ) - 1 / 2) ^ 2 ≤ k + 1:= by linarith
      replace h2 : k + 1 < ((m : ℝ) + 1 / 2) ^ 2:= by linarith
      replace h1 : √(((m : ℝ) - 1 / 2) ^ 2) ≤ √(k + 1):= by exact Real.sqrt_le_sqrt h1
      replace h2 : √(k + 1) < √(((m : ℝ) + 1 / 2) ^ 2):= by exact Real.sqrt_lt_sqrt (by positivity) h2
      -- Show that the expressions under square roots are non-negative
      have g1 : (m : ℝ) - 1 / 2 ≥ 0:= by rify at hm ; linarith
      have g2 : (m : ℝ) + 1 / 2 ≥ 0:= by rify at hm ; linarith
      set r:= (1 : ℝ) / 2 with hr
      clear_value r
      field_simp at h1 h2
      subst r
      -- Use the definition of round to complete the proof
      rw [round_eq _]
      refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
      all_goals
        linarith
  -- Set M to be round(√N) and extract its properties
  set M:= round (√N) with hM
  clear_value M
  rw [show N = N - 1 + 1 by omega] at hM
  simp at hM
  replace hM:= (h1 (N - 1) M).1 (by rw [hM])
  set n:= N - 1 with hn
  clear_value n
  replace hN : N = n + 1:= by omega
  subst N
  -- Set m to be the absolute value of M
  set m:= M.natAbs with hm
  clear_value m
  rcases hM with ⟨hM1, hM2⟩
  -- Show that M ≥ 1
  have hMpos : M ≥ 1:= by
    by_contra H
    replace H : M ≤ 0:= by linarith
    linarith
  -- Show that m ≥ 1
  have hmpos : m ≥ 1:= by
    subst m
    zify
    rw [abs_of_nonneg (by linarith)]
    exact hMpos
  -- Prove that n ≥ m²-m
  have hm1 : n ≥ m ^ 2 - m:= by
    have g : m * m ≥ 1 * m:= by exact Nat.mul_le_mul_right m hmpos
    ring_nf at g
    zify
    field_simp
    subst m
    simp
    rw [abs_of_nonneg (by linarith)]
    linarith
  -- Prove that n < m²+m
  have hm2 : n < m ^ 2 + m:= by
    subst m
    zify
    simp
    rw [abs_of_nonneg (by linarith)]
    linarith
  simp
  zify at hm
  rw [abs_of_nonneg (by linarith)] at hm
  rw [←hm]
  clear hM1 hM2 hMpos hn hm M
  -- Use the fact that m² ≥ m to simplify
  have g : m * m ≥ 1 * m:= by exact Nat.mul_le_mul_right m hmpos
  ring_nf at g
  -- Set r to be the remainder: n - (m²-m)
  set r:= n - (m ^ 2 - m) with hr
  clear_value r
  replace hr : n = m ^ 2 - m + r:= by omega
  -- Show that r < 2m
  have hr1 : r < 2 * m:= by omega
  clear hm1 hm2
  subst n
  field_simp
  -- Lemma: sum can be split into two parts
  have h2 : ∀ t : ℕ, ∑ k ∈ Finset.range (m ^ 2 - m + t), (1 : ℝ) / a (k + 1) = ∑ k ∈ Finset.range (m ^ 2 - m), (1 : ℝ) / a (k + 1) + ∑ k ∈ Finset.range t, (1 : ℝ) / a (m ^ 2 - m + k + 1):= by
    intro t
    induction t with
    | zero =>
      simp
    | succ t ih =>
      rw [Finset.sum_range_succ]
      rw [show m ^ 2 - m + (t + 1) = m ^ 2 - m + t + 1 by ring]
      rw [Finset.sum_range_succ]
      linarith
  -- Key result: sum up to m²-m equals 2(m-1)
  have h3 : ∑ k ∈ Finset.range (m ^ 2 - m), (1 : ℝ) / a (k + 1) = 2 * (m - 1):= by
    set t:= m - 1 with ht
    clear_value t
    replace ht : m = t + 1:= by omega
    subst m
    simp
    rw [show (t + 1) ^ 2 - (t + 1) = t * (t + 1) by ring_nf ; omega]
    -- Prove by induction that sum up to t(t+1) equals 2t
    have h3 : ∀ t : ℕ, ∑ k ∈ Finset.range (t * (t + 1)), (1 : ℝ) / a (k + 1) = 2 * ↑t:= by
      intro t
      induction t with
      | zero =>
        simp
      | succ t ih =>
        rw [show (t + 1) * (t + 1 + 1) = t * (t + 1) + 2 * (t + 1) by ring_nf]
        simp
        -- Lemma for splitting sums
        have h4 : ∀ s : ℕ, ∑ k ∈ Finset.range (t * (t + 1) + s), (1 : ℝ) / a (k + 1) = ∑ k ∈ Finset.range (t * (t + 1)), (1 : ℝ) / a (k + 1) + ∑ k ∈ Finset.range s, (1 : ℝ) / a (t * (t + 1) + k + 1):= by
          intro s
          induction s with
          | zero =>
            simp
          | succ s ih =>
            rw [show t * (t + 1) + (s + 1) = t * (t + 1) + s + 1 by ring_nf]
            rw [Finset.sum_range_succ]
            rw [Finset.sum_range_succ]
            linarith
        field_simp
        rw [h4 (2 * (t + 1))]
        clear h4
        rw [ih]
        -- Show that for the next 2(t+1) terms, a_k = t+1
        have h3 : ∀ k ∈ Finset.range (2 * (t + 1)), 1 / a (t * (t + 1) + k + 1) = (1 : ℝ) / (t + 1):= by
          intro k hk
          simp at hk
          zify at hk
          suffices a (t * (t + 1) + k + 1) = t + 1 by rw [this] ; simp
          replace h1:= (h1 (t * (t + 1) + k) (t + 1)).2
          rw [ha (t * (t + 1) + k + 1)]
          simp at h1 ⊢
          apply h1
          linarith
          linarith
        replace h3 : ∑ k ∈ Finset.range (2 * (t + 1)), (1 : ℝ) / a (t * (t + 1) + k + 1) = ∑ k ∈ Finset.range (2 * (t + 1)), (1 : ℝ) / (t + 1):= by exact Finset.sum_congr rfl h3
        rw [h3]
        field_simp
        linarith
    field_simp
    exact h3 t
  -- Apply the splitting lemma with t = r+1
  specialize h2 (r + 1)
  rw [show m ^ 2 - m + (r + 1) = m ^ 2 - m + r + 1 by ring] at h2
  -- Show that the remaining r+1 terms all have a_k = m
  have h4 : ∑ k ∈ Finset.range (r + 1), (1 : ℝ) / (a (m ^ 2 - m + k + 1)) = ∑ _ ∈ Finset.range (r + 1), (1 : ℝ) / m:= by
    suffices ∀ k ∈ Finset.range (r + 1), (1 : ℝ) / (a (m ^ 2 - m + k + 1)) = 1 / m by exact Finset.sum_congr rfl this
    intro k hk
    suffices a (m ^ 2 - m + k + 1) = m by rw [this] ; simp
    rw [ha (m ^ 2 - m + k + 1)]
    specialize h1 (m ^ 2 - m + k) m
    field_simp at h1 ⊢
    replace h1:= h1.2
    apply h1
    simp at hk
    zify at hk hr1
    linarith
  -- Combine all the results to get the final formula
  rw [h2, h3, h4]
  field_simp
  linarith
