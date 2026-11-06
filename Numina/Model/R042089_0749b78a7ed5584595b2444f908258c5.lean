import Mathlib

open Finset

theorem number_theory_706 (n: ℕ): ∑ i ∈ range (n + 1) \ {0}, Nat.log 2 i = 1994 ↔ n = 312 := by 
  constructor
  · -- Assume the sum equals 1994, prove n = 312
    intro h
    have h1 : n ≤ 312 := by
      by_contra h2
      push_neg at h2 
      have h3 : n ≥ 313 := by omega 
      have h4 : ∑ i ∈ range (n + 1) \ {0}, Nat.log 2 i ≥ ∑ i ∈ range 314 \ {0}, Nat.log 2 i := by 
        have h5 : range (n + 1) ≥ range 314 := by 
          intro x hx 
          simp at hx ⊢ 
          omega 
        have h6 : range 314 \ {0} = range 314 \ {0} := by rfl 
        have h7 : range (n + 1) \ {0} = range (n + 1) \ {0} := by rfl 
        apply sum_le_sum_of_subset_of_nonneg 
        · -- Show range 314 \ {0} ⊆ range (n + 1) \ {0}
          intro x hx 
          simp at hx ⊢ 
          omega 
        · -- Show that each term is non-negative 
          intro i hi 
          simp 
          all_goals omega 
      have h5 : ∑ i ∈ range 314 \ {0}, Nat.log 2 i > 1994 := by 
        native_decide 
      have h6 : ∑ i ∈ range (n + 1) \ {0}, Nat.log 2 i > 1994 := by 
        linarith 
      linarith 
    have h2 : n ≥ 312 := by 
      by_contra h2 
      push_neg at h2 
      have h3 : n < 312 := by omega 
      have h4 : ∑ i ∈ range (n + 1) \ {0}, Nat.log 2 i < 1994 := by 
        interval_cases n <;> try { 
          native_decide 
        } 
      linarith 
    have h3 : n = 312 := by linarith 
    assumption 
  · -- Assume n = 312 
    intro h4 
    rw [h4]
    native_decide