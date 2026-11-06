import Mathlib

/- Table E.

The sum of $n$ numbers is zero, and the sum of their squares is one. Prove that among these numbers, there are two whose product is no greater than $-1 / n$.

# -/
theorem algebra_208346 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (h₀ : ∑ i, a i = 0) (h₁ : ∑ i, (a i)^2 = 1) :
    ∃ i j, i ≠ j ∧ a i * a j ≤ -1 / n := by
      -- We first find the maximum and minimum elements among the numbers.
      have := @Finite.exists_max (Fin n) ℝ (Finite.of_fintype (Fin n)) (Fin.pos_iff_nonempty.mp hn) _ a
      rcases this with ⟨M, hM⟩
      have := @Finite.exists_min (Fin n) ℝ (Finite.of_fintype (Fin n)) (Fin.pos_iff_nonempty.mp hn) _ a
      rcases this with ⟨m, hm⟩
      -- We show that the maximum and minimum elements are different.
      have hneq : m ≠ M := by
        intro heq
        have : ∀ i, a i = a m := by
          intro i
          have h1 := hm i
          have h2 := hM i
          rw [← heq] at h2
          linarith
        -- If all elements are equal, their sum must be zero, leading to a contradiction.
        have : ∑ i:Fin n, a i = n * a m := by
          calc
            _ = ∑ i:Fin n, a m := by
              congr
              ext i
              exact this i
            _ = ∑ i:Fin n, 1 * a m := by ring_nf
            _ = (∑ i:Fin n, 1) * a m := by
              exact Eq.symm (Finset.sum_mul Finset.univ (fun i => 1) (a m))
            _ = _ := by simp
        rw [h₀] at this
        simp at this
        rcases this with h1 | h2
        · linarith
        -- If all elements are zero, their squares sum to zero, contradicting the assumption.
        · have : ∑ i: Fin n, a i ^ 2 = 0 := by
            calc
              _ = ∑ i:Fin n, (0:ℝ) := by
                congr
                ext i
                rw [this i, h2]
                simp
              _ = _ := by simp
          rw [this] at h₁
          norm_num at h₁
      -- Consider the expression involving differences from the min and max.
      have hle: ∀ i, (a m - a i) * (a M - a i) ≤ 0 := by
        intro i
        have h1 : a m - a i ≤ 0 := by
          have := hm i
          linarith
        have h2 : a M - a i ≥ 0 := by
          have := hM i
          linarith
        exact mul_nonpos_of_nonpos_of_nonneg h1 h2
      -- The sum of these expressions over all elements is non-positive.
      have hle' : ∑ i, (a m - a i) * (a M - a i) ≤ 0 := by
        exact Fintype.sum_nonpos hle
      -- Expand the sum to relate it to the given conditions.
      have heq :  ∑ i, (a m - a i) * (a M - a i) = (∑ i: Fin n, a m * a M) + (∑ i, (a i)^2) - (∑ i, a i) * a m - (∑ i, a i) * a M := by
        calc
          _ = ∑ i:Fin n, (a m * a M + (a i)^2 - a i * a m - a i * a M) := by
            congr
            ext i
            ring
          _ = (∑ i:Fin n, a m * a M) + (∑ i, (a i)^2) - (∑ i, a i * a m) - (∑ i, a i * a M) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
          _ = _ := by
            rw [Eq.symm (Finset.sum_mul Finset.univ a (a m))]
            rw [Eq.symm (Finset.sum_mul Finset.univ a (a M))]
      -- Substitute the known sums into the equation.
      rw [h₀, h₁] at heq
      rw [heq] at hle'
      simp at hle'
      -- Conclude that the product of the min and max is sufficiently negative.
      use m
      use M
      constructor
      · exact hneq
      · have : n * (a m * a M) ≤ -1 := by linarith
        calc
          _ = n * (a m * a M) / n := by
            refine Eq.symm (mul_div_cancel_left₀ (a m * a M) ?ha)
            norm_cast
            intro h
            rw [h] at hn
            norm_num at hn
          _ ≤ _ := by apply (div_le_div_iff_of_pos_right (by norm_cast)).mpr this
