import Mathlib

theorem algebra_6355 :
    ∃r : Finset ℕ, r = {m : ℕ | ∃n : ℕ, n > 0 ∧ m > 0 ∧ ∑i ∈ Finset.range (m + 1), (n + i) = 2020} ∧ r.sum id = 50 := by

  have h1 : {m : ℕ | ∃n : ℕ, n > 0 ∧ m > 0 ∧ ∑i ∈ Finset.range (m + 1), (n + i) = 2020} = {4, 7, 39} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First, we'll prove that if exists n, then m in {4,7,39}
      intro h
      rcases h with ⟨n, hn, hm, heq⟩
      have h2 : m ≤ 63 := by
        by_contra h
        push_neg at h
        have h3 : ∑i in Finset.range (m + 1), (n + i) > 2020 := by
          have h4 : m ≥ 64 := by omega
          have h5 : ∑i in Finset.range (m + 1), (n + i) ≥ ∑i in Finset.range 65, (n + i) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · -- Show that Finset.range 65 ⊆ Finset.range (m + 1)
              intro i hi
              simp at hi ⊢
              omega
            · -- Show that each term is non-decreasing
              intro i hi
              simp
          have h6 : ∑i in Finset.range 65, (n + i) > 2020 := by
            norm_num [Finset.sum_range_succ]
            all_goals omega
          linarith
        linarith [heq, h3]
      interval_cases m <;> norm_num [Finset.sum_range_succ] at heq ⊢
      <;> omega
    · -- Now, we'll prove the reverse.
      rintro (rfl | rfl | rfl)
      · -- m = 4
        use 402
        native_decide
      · -- m = 7
        use 249
        native_decide
      · -- m = 39
        use 31
        native_decide

  rw [h1]
  use {4, 7, 39}
  constructor
  · -- Show the equality
    ext m
    simp
  · -- Show the sum
    native_decide