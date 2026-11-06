import Mathlib

/- 3. To determine 11 real numbers such that each of them is equal to the square of the sum of the remaining 10. -/

theorem algebra_214355 (x : Fin 11 → ℝ) (h : ∀ i, x i = (∑ j in Finset.univ \ {i}, x j) ^ 2) :
    (∀ i, x i = 0) ∨ (∀ i, x i = 1/100) := by

  -- We give a name to the sum of all 11 numbers for convenience.
  let s := ∑ i, x i
  have hs : s = ∑ i, x i := by rfl

  -- We rewrite the hypothesis in terms of `s`.
  have h' : ∀ i, x i = (s - x i) ^ 2 := by
    intro i
    rw [hs, Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i) x]
    ring_nf; simp_rw [← h i]

  -- We will assume that all numbers are equal, and that the converse leads to a contradiction.
  by_cases hij : ∀ i j, x i = x j
  -- If all numbers are equal, then they are all equal to x 0.
  · have : x 0 = (10 * x 0) ^ 2 := by
      rw [(by simp [hs, hij _ 0] : s = 11 * x 0)] at h'
      nth_rw 1 [h' 0]
      ring
    -- We can solve this equation to find the possible values of x 0.
    have : x 0 = 0 ∨ x 0 = 1/100 := by
      have : (100 * (x 0) - 1) * x 0 = 0 := by
        ring_nf; nth_rw 1 [this]; ring
      rcases mul_eq_zero.mp this with (h | h)
      · right; apply eq_one_div_of_mul_eq_one_right; exact sub_eq_zero.mp h
      · left; exact h
    -- x 0 is a solution to the quadratic equation, so it is either 0 or 1/100.
    -- It follows that that all numbers are equal to 0 or 1/100.
    by_cases h : x 0 = 0
    · left; rw [← h]; exact fun i ↦ hij i 0
    · right; simp only [Fin.isValue, h, false_or] at this; rw [← this]; exact fun i ↦ hij i 0

  -- If not all numbers are equal, we find a contradiction.
  · -- The numbers are all non-negative, because they are equal to a square.
    have xpos (i : Fin 11) : x i >= 0 := by rw [h i]; exact sq_nonneg (∑ j ∈ Finset.univ \ {i}, x j)
    -- Let i and j be two indices such that x i ≠ x j.
    obtain ⟨i, j, neq⟩ : ∃ i j, x i ≠ x j := by
      by_contra! h
      apply hij
      exact h
    -- Wlog assume that x i < x j.
    wlog lt : x i < x j
    · exact this x h hs h' hij xpos j i neq.symm (lt_of_le_of_ne (le_of_not_lt lt) neq.symm)
    · -- We have (s - x i)^2 < (s - x j)^2 because they are equal to x i and x j respectively.
      have : (s - x i)^2 < (s - x j)^2 := by
        rw [← h' i, ← h' j]
        exact lt
      -- But we also have (s - x i)^2 > (s - x j)^2 because x i < x j.
      have : (s - x i)^2 > (s - x j)^2 := by
        refine (sq_lt_sq₀ ?_ ?_).mpr (by linarith : s - x i > s - x j)
        · rw [hs, Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j) x]
          ring_nf; exact Finset.sum_nonneg fun i a ↦ xpos i
        · rw [hs, Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i) x]
          ring_nf; exact Finset.sum_nonneg fun i a ↦ xpos i
      -- This is a contradiction.
      linarith