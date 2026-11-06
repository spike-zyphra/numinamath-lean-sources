import Mathlib

theorem algebra_929 :
    IsGreatest {m | ∃ n : ℕ, n > 0 ∧ (∑ i ∈ Finset.range m, (n + i)) ≤ 400} 27 := by
  constructor
  · -- Show that 27 is in the set, with n = 1.
    use 1
    native_decide
  · -- Show that 27 is the greatest in the set.
    intro m hm
    rcases hm with ⟨n, hn, hsum⟩
    by_contra h
    push_neg at h
    have h1 : m ≥ 28 := by omega
    have h2 : ∑ i in Finset.range m, (n + i) > 400 := by
      have h3 : m ≥ 28 := by omega
      have h4 : ∑ i in Finset.range 28, (n + i) > 400 := by
        norm_num [Finset.sum_range_succ] at *
        all_goals 
          omega
      have h5 : ∑ i in Finset.range m, (n + i) ≥ ∑ i in Finset.range 28, (n + i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (show Finset.range 28 ⊆ Finset.range m by 
          intro i hi
          simp at hi ⊢
          omega 
        ) 
        intro i hi 
        simp at hi ⊢
      linarith [h4, h5]
    linarith