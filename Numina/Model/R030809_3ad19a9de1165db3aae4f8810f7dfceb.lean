import Mathlib

theorem number_theory_120002 (a b c : Finset ℕ) (h₀ : a ∪ b ∪ c = Finset.Icc 1 8)
    (h₁ : a ∩ b = ∅) (h₂ : a ∩ c = ∅) (h₃ : b ∩ c = ∅)
    (h₄ : ∑ x ∈ a, x ≠ ∑ x ∈ b, x) (h₅ : ∑ x ∈ a, x ≠ ∑ x ∈ c, x)
    (h₆ : ∑ x ∈ b, x ≠ ∑ x ∈ c, x) (h₇ : max (max (∑ x ∈ a, x) (∑ x ∈ b, x)) (∑ x ∈ c, x) =
    2 * min (min (∑ x ∈ a, x) (∑ x ∈ b, x)) (∑ x ∈ c, x)) :
    min (min (∑ x ∈ a, x) (∑ x ∈ b, x)) (∑ x ∈ c, x) = 8 := by
  have h12 : ∑ x in a, x + ∑ x in b, x + ∑ x in c, x = 36 := by
    have h13 : ∑ x in a ∪ b ∪ c, x = ∑ x in a, x + ∑ x in b, x + ∑ x in c, x := by
      have h14 : ∑ x in a ∪ b, x = ∑ x in a, x + ∑ x in b, x := by
        apply Finset.sum_union
        have h15 : Disjoint a b := by
          rw [Finset.disjoint_iff_inter_eq_empty]
          exact h₁
        exact h15
      have h15 : Disjoint (a ∪ b) c := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        have h22 : (a ∪ b) ∩ c = ∅ := by
          have h5 : a ∩ c = ∅ := h₂
          have h6 : b ∩ c = ∅ := h₃
          rw [Finset.union_inter_distrib_right]
          rw [h5, h6]
          simp
        exact h22
      have h14' : ∑ x in (a ∪ b) ∪ c, x = ∑ x in (a ∪ b), x + ∑ x in c, x := by
        apply Finset.sum_union
        exact h15
      rw [show (a ∪ b ∪ c) = (a ∪ b) ∪ c by rfl]
      rw [h14']
      rw [h14]
    have h14 : ∑ x in Finset.Icc 1 8, x = 36 := by
      norm_num [Finset.sum_Icc_succ_top]
    rw [h₀] at h13
    linarith
  have h13 : ∑ x in a, x + ∑ x in b, x + ∑ x in c, x = 36 := h12
  -- Apply the theorem condition h₇ and total sum h12 to show the answer.
  -- Suppose the minimum sum is $8$, then the maximum sum is $16$, and the total sum is 36 so the third group sum is 12.
  -- This is the only possible sum satisfying all the constraints.
  -- We use omega to solve the arithmetic.
  have h80 : min (min (∑ x ∈ a, x) (∑ x ∈ b, x)) (∑ x ∈ c, x) = 8 := by
    -- $\max(\max(s_a, s_b), s_c) = 2 \cdot \min(\min(s_a, s_b), s_c)$
    -- and total sum 36 gives the answer.
    -- Let's suppose that $\min(s_a, s_b, s_c) = k$.
    -- Then the max sum $= 2k$.
    -- So $k + m + 2k = 36$, where $k < m < 2k$.
    -- We get $3k + m = 36$.
    -- $m = 36 - 3k$.
    -- $k < 36 - 3k < 2k$.
    -- Solving the left inequality: $4k < 36$ => $k < 9$.
    -- Solving the right inequality: $36 - 3k < 2k$ => $36 < 5k$ => $k > 36/5 = 7.2$.
    -- So $7.2 < k < 9$, so $k = 8$.
    -- Therefore $k = 8$.
    -- Now all conditions must be satisfied.
    -- We can solve using Lean's omega.
    omega
  exact h80