import Mathlib
theorem algebra_167304 : IsGreatest {n : ℕ | ∃ a : ℕ → ℝ, (∀ i ∈ Finset.range n, a i = a 0 + 4 * i) ∧ a 0 ^ 2 - a 0 + ∑ i in Finset.range n, a i ≤ 100} 8:= by
  constructor
  · -- Show 8 is in the set
    use fun i => -3.5 + 4 * (i : ℝ)
    constructor
    · -- Show it's an arithmetic sequence with common difference 4
      intro i hi
      simp at hi ⊢
      all_goals linarith
    · -- Verify the inequality
      norm_num [Finset.sum_range_succ]
      all_goals norm_num
  · -- Show no larger element is in the set
    intro n hn
    rcases hn with ⟨a, ha1, ha2⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 9 := by omega
    have h2 : ∀ i ∈ Finset.range n, a i = a 0 + 4 * (i : ℝ) := by 
      intro i hi 
      specialize ha1 i hi 
      simpa using ha1 
    have h3 : ∑ i in Finset.range n, a i = (n : ℝ) * a 0 + 2 * (n : ℝ) * ((n : ℝ) - 1) := by
      have h4 : ∀ i : ℕ, i ∈ Finset.range n → a i = a 0 + 4 * (i : ℝ) := by 
        intro i hi 
        apply h2 i hi 
      have h5 : ∑ i in Finset.range n, a i = ∑ i in Finset.range n, (a 0 + 4 * (i : ℝ)) := by 
        apply Finset.sum_congr 
        · -- Show the index set is the same 
          rfl 
        · -- Show the function is the same 
          intro i hi 
          exact h4 i hi 
      rw [h5] 
      have h6 : ∑ i in Finset.range n, (a 0 + 4 * (i : ℝ)) = (n : ℝ) * a 0 + 2 * (n : ℝ) * ((n : ℝ) - 1) := by 
        have h7 : ∀ (n : ℕ), ∑ i in Finset.range n, (a 0 + 4 * (i : ℝ)) = (n : ℝ) * a 0 + 2 * (n : ℝ) * ((n : ℝ) - 1) := by 
          intro n 
          induction n with 
          | zero => 
            simp 
          | succ n ih => 
            rw [Finset.sum_range_succ, ih] 
            field_simp 
            ring 
        specialize h7 n 
        simpa using h7 
      linarith [h6] 
    rw [h3] at ha2 
    have h4 : (n : ℝ) ≥ 9 := by 
      exact_mod_cast h1 
    nlinarith [sq_nonneg (a 0 + (n - 1) / 2), sq_nonneg ((n : ℝ) - 9), sq_nonneg (a 0 + 4 * (n - 1)), sq_nonneg (a 0 - (- (n - 1))), sq_nonneg (a 0 + 2 * (n - 1)), sq_nonneg (a 0 + (n - 1) + 4 * (n - 1)), sq_nonneg (a 0 - 4 * (n - 1) - (n - 1)), sq_nonneg (a 0 - 2 * (n - 1) - (n - 1))]