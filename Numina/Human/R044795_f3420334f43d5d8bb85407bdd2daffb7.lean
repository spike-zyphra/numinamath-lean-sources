import Mathlib


/- (BXMO P1 2022)

Let $n \geqslant 0$ and $a_{0}, \ldots, a_{n} \in \mathbb{R}$. Show that there exists $k \in \llbracket 0, n \rrbracket$ such that for all $x \in[0,1]$, we have $\sum_{i=0}^{n} a_{i} x^{i} \leqslant \sum_{i=0}^{k} a_{i}$. -/
theorem inequalities_131034 {n : ℕ} (a : ℕ → ℝ) :
  ∃ k ∈ Finset.Icc 0 n, ∀ x ∈ Set.Icc 0 1, ∑ i in Finset.range (n+1), a i * x ^ i ≤ ∑ i in Finset.range (k+1), a i
  := by
    -- We prove by induction on n
    induction' n with p ph generalizing a
    -- n = 0 is trivial
    · simp only [Finset.Icc_self, Finset.mem_singleton, Set.mem_Icc, zero_add, Finset.range_one,
      Finset.sum_singleton, pow_zero, mul_one, and_imp, exists_eq_left, le_refl, implies_true]
    -- in the induction step, we shift a by 1
    · obtain ⟨k, kh1, kh2⟩ := ph (fun x => a (x + 1))
      -- We prove an upper bound that doesn't contain x
      have max_upper : ∀ x ∈ Set.Icc 0 1, ∑ i ∈ Finset.range (p + 1 + 1), a i * x ^ i
        ≤ max (a 0) (∑ i ∈ Finset.range (k + 1 + 1), a i)
      · intro x xh
        replace kh2 := kh2 x xh
        calc ∑ i ∈ Finset.range (p + 1 + 1), a i * x ^ i
        _ = a 0 + ∑ i ∈ Finset.range (p + 1), a (i+1) * x ^ (i+1) := by
          rw [Finset.sum_range_succ', pow_zero, mul_one, add_comm]
        _ = a 0 + ∑ i ∈ Finset.range (p + 1), x * (a (i+1) * x ^ i) := by
          congr
          ext i
          ring_nf
        _ = a 0 + x * ∑ i ∈ Finset.range (p + 1), a (i+1) * x ^ i := by
          congr
          exact (Finset.mul_sum _ _ x).symm
        _ ≤ max (a 0) (a 0 + ∑ i ∈ Finset.range (p + 1), a (i+1) * x ^ i) := by
          -- a + x * b has an upper bound which doesn't contain x
          have sum_le_max : ∀ {a b : ℝ}, a + x * b ≤ max a (a + b)
          · intro a b
            simp only [Set.mem_Icc] at xh
            have ⟨xh1, xh2⟩ := xh
            by_cases h : b ≤ 0
            · simp only [add_le_iff_nonpos_right, h, sup_of_le_left]
              exact mul_nonpos_of_nonneg_of_nonpos xh1 h
            · simp only [le_sup_iff, add_le_iff_nonpos_right, add_le_add_iff_left]
              exact Or.inr <| (mul_le_iff_le_one_left <| not_le.mp h).mpr xh2
          exact sum_le_max
        -- induction hypothesis
        _ ≤ max (a 0) (a 0 + ∑ i ∈ Finset.range (k + 1), a (i + 1)) := by
          simp only [le_sup_iff, sup_le_iff, le_refl, add_le_iff_nonpos_right, true_and,
            le_add_iff_nonneg_right, add_le_add_iff_left, kh2, and_true]
          by_cases h : ∑ i ∈ Finset.range (p + 1), a (i + 1) * x ^ i ≤ 0
          · tauto
          · exact Or.inr <| le_trans (le_of_not_ge h) kh2
        -- simplify
        _ = max (a 0) (∑ i ∈ Finset.range (k + 1 + 1), a i) := by
          congr
          rw [add_comm]
          exact Eq.symm (Finset.sum_range_succ' a (k + 1))

      -- Then we have that both upper bounds can be expressed as wanted
      -- either k' = k + 1 or k' = 0
      by_cases h : a 0 ≤ ∑ i ∈ Finset.range (k + 1 + 1), a i
      · simp only [h, sup_of_le_right] at max_upper
        refine ⟨k+1, ?_, max_upper⟩
        simpa only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, add_le_add_iff_right,
          true_and] using kh1
      · simp only [le_of_lt <| not_le.mp h, sup_of_le_left] at max_upper
        refine ⟨0, Finset.insert_eq_self.mp rfl, ?_⟩
        · rw [zero_add, Finset.range_one, Finset.sum_singleton]
          exact max_upper