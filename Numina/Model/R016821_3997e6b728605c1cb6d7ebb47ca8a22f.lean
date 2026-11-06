import Mathlib

theorem algebra_116976 (n : ℕ) (h₀ : n > 0) (h₁ : ∑ i ∈ Finset.range n, (264 - i) = 264 * n - 187) :
    n = 11 := by
  have h24 : n ≤ 21 := by
    by_contra h 
    push_neg at h 
    have h3 : n ≥ 22 := by linarith 
    have h6 : ∑ i in Finset.range n, (264 - i) < 264 * n - 187 := by 
      have h9 : ∀ k : ℕ, ∑ i in Finset.range (k + 22), (264 - i) < 264 * (k + 22) - 187 := by
        intro k 
        induction k with 
        | zero => 
          norm_num [Finset.sum_range_succ]
        | succ k ih => 
          rw [Finset.sum_range_succ] 
          simp at ih ⊢ 
          all_goals 
            omega 
      specialize h9 (n - 22) 
      have h10 : (n - 22 + 22 : ℕ) = n := by 
        omega 
      rw [show n - 22 + 22 = n by omega] at h9 
      linarith 
    omega 
  interval_cases n <;> try { 
    norm_num [Finset.sum_range_succ] at h₁ 
    all_goals 
      omega 
  }