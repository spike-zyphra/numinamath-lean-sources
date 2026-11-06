import Mathlib

theorem number_theory_22925 : IsLeast {leaves : ℕ | ∃ pages : ℕ, pages = 2 * leaves ∧ ∃ k : ℕ, pages = 7 * k + 3 ∧ 100 < leaves} 103 := by 
  constructor
  · -- Show that 103 is in the set.
    use 206
    constructor
    · -- Show that pages = 2 * leaves
      norm_num
    · -- Show that there's a k such that pages = 7 * k + 3 and 100 < leaves
      use 29
      all_goals
      norm_num
  · -- Show that for any element in the set, it's ≥ 103.
    intro leaves h
    rcases h with ⟨pages, hp1, k, hp2, h1⟩
    by_contra h2
    push_neg at h2
    have h3 : leaves > 100 := by linarith
    have h4 : leaves = 101 ∨ leaves = 102 := by 
      omega 
    rcases h4 with (r | r)
    · -- leaves = 101
      have h5 : leaves = 101 := r
      have h6 : pages = 202 := by 
        rw [show pages = 2 * leaves by omega, h5]
        all_goals
          omega 
      rw [h6] at hp2
      omega
    · -- leaves = 102
      have h5 : leaves = 102 := r
      have h6 : pages = 204 := by
        rw [show pages = 2 * leaves by omega, h5]
        all_goals
          omega 
      rw [h6] at hp2
      omega