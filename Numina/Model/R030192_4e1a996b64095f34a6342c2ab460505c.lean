import Mathlib

-- Suppose that |x_i| < 1 for i = 1, 2, …, n. Suppose further that |x_1| + |x_2| + ⋯ + |x_n| = 19 + |x_1 + x_2 + ⋯ + x_n|. What is the smallest possible value of n?

theorem algebra_95331 : IsLeast {n : ℕ | ∃ (x : Fin n → ℝ), (∀ i, |x i| < 1) ∧
    (∑ i, |x i| = 19 + |∑ i, x i|)} 20 := by
  constructor
  · -- Show 20 is in the set
    use λ i =>
      if i.val < 10 then (0.95 : ℝ) else (-0.95 : ℝ)
    constructor
    · -- Show that for all i, |x i| < 1
      intro i
      fin_cases i <;> norm_num [abs_of_pos, abs_of_neg]
    · -- Show that the sum of absolute values is 19 + total sum
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      all_goals norm_num [abs_of_pos, abs_of_neg]
  · -- Show that 20 is minimal
    intro n hn
    rcases hn with ⟨x, hx1, hx2⟩
    by_contra h
    push_neg at h
    have h19 : n ≤ 19 := by linarith
    by_cases hn0 : n = 0
    · -- Case n = 0
      subst n
      simp at hx2 
    · -- Case n ≠ 0
      have hn_pos : n > 0 := by 
        by_contra h'
        push_neg at h'
        have : n = 0 := by linarith
        contradiction 
      -- Show that ∑ i : Fin n, |x i| < (n : ℝ)
      have h3 : ∑ i : Fin n, |x i| < (n : ℝ) := by
        have h4 : ∀ i : Fin n, |x i| < 1 := hx1 
        have h5 : ∑ i : Fin n, |x i| < ∑ i : Fin n, (1 : ℝ) := by
          apply Finset.sum_lt_sum 
          · -- Show that |x i| ≤ 1 for all i 
            intro i hi 
            have h6 : |x i| < 1 := h4 i 
            have h7 : |x i| ≤ (1 : ℝ) := by linarith [abs_nonneg (x i), h6] 
            simpa using h7 
          · -- Show that there exists an index i such that |x i| < 1 
            use ⟨0, by omega⟩ 
            have h8 : |x ⟨0, by omega⟩| < 1 := h4 ⟨0, by omega⟩ 
            simpa using h8 
        have h6 : ∑ i : Fin n, (1 : ℝ) = (n : ℝ) := by 
          simp 
        linarith [h6] 
      have h3' : (n : ℝ) ≤ 19 := by exact_mod_cast h19 
      have h7 : ∑ i : Fin n, |x i| ≥ 19 := by 
        have h8 : ∑ i : Fin n, |x i| = 19 + |∑ i : Fin n, x i| := by 
          linarith 
        have h9 : |∑ i : Fin n, x i| ≥ 0 := abs_nonneg (∑ i : Fin n, x i) 
        linarith 
      have h8 : (n : ℝ) > 19 := by 
        linarith [h3, h7] 
      have h9 : n ≥ 20 := by 
        by_contra h 
        push_neg at h 
        have h10 : n ≤ 19 := by linarith 
        have h11 : (n : ℝ) ≤ (19 : ℝ) := by exact_mod_cast h10 
        linarith 
      linarith