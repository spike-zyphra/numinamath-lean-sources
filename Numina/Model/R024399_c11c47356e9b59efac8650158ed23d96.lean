import Mathlib

theorem number_theory_32448 (p n : ℕ) (hp : Nat.Prime p) (hn : p < n) :
    ∃ k, k > 0 ∧ n ^ (n - p) = k ^ n ↔ (p, n) = (4, 2) := by
  by_cases h : (p, n) = (4, 2)
  · -- Suppose (p, n) = (4, 2)
    use 4  -- Then k =4, from definition of pair (4, 2) equals n. 
    simp [Prod.ext_iff] at h ⊢
    rcases h with ⟨rfl, rfl⟩
    all_goals
      try { 
        tauto
      }
      <;> try { 
            omega 
          }
  · -- Now (p, n) ≠ (4, 2)
    use 0 
    simp at *
    all_goals
      try { 
        tauto
      }
      <;> try { 
            omega 
          }