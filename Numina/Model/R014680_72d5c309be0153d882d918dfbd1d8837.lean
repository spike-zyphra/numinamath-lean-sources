import Mathlib

open BigOperators Real Set

theorem inequalities_274318 {n : ℕ} (hn : n ≥ 4) (lambda : ℝ)
  (hlambda : lambda = ∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1)) :
  lambda ≥ 2 * sin ((n - 2) / (2 * n) * π) := by
  have h1 : n ≥ 4 := by linarith
  have h3 : lambda = ∑ i in Finset.range n, (1 : ℝ) / (i + 1) := by linarith [hlambda]
  have h4 : (∑ i in Finset.range n, (1 : ℝ) / (i + 1)) ≥ (2 : ℝ) := by
    have h5 : n ≥ 4 := by linarith
    have h8 : (∑ i in Finset.range n, (1 : ℝ) / (i + 1)) ≥ (2 : ℝ) := by
      have h9 : ∀ (k : ℕ), k ≥ 4 → (∑ i in Finset.range k, (1 : ℝ) / (i + 1)) ≥ (2 : ℝ) := by
        intro k hk
        have base4 : (∑ i in Finset.range 4, (1 : ℝ) / (i + 1)) ≥ (2 : ℝ) := by
          norm_num [Finset.sum_range_succ]
        have step4 : ∀ (j : ℕ), j ≥ 4 → (∑ i in Finset.range j, (1 : ℝ) / (i + 1)) ≥ (2 : ℝ) → (∑ i in Finset.range (j + 1), (1 : ℝ) / (i + 1)) ≥ (2 : ℝ) := by
          intro j h10 h11
          have h17 : (∑ i in Finset.range (j + 1), (1 : ℝ) / (i + 1)) = (∑ i in Finset.range j, (1 : ℝ) / (i + 1)) + (1 : ℝ) / ((j) + 1) := by
            rw [Finset.sum_range_succ]
          rw [h17]
          have h18 : (1 : ℝ) / ((j) + 1) ≥ 0 := by
            have h45 : (j + 1 : ℝ) > 0 := by
              have h40 : (j : ℝ) ≥ (4 : ℝ) := by exact_mod_cast (show j ≥ 4 by linarith)
              nlinarith
            apply div_nonneg
            all_goals linarith
          nlinarith
        exact Nat.le_induction base4 step4 k (by omega)
      specialize h9 n (by linarith)
      linarith
    linarith
  have h5 : (2 * sin ((n - 2) / (2 * n) * π)) ≤ (2 : ℝ) := by
    have h8 : sin ((n - 2) / (2 * n) * π) ≤ (1 : ℝ) := by
      apply sin_le_one
    nlinarith
  rw [h3]
  nlinarith [h4, h5]