import Mathlib

theorem number_theory_52936 (n : ℕ) (hn : 3 ≤ n) :
    ∃ k, ∃ m, n = ∑ i ∈ Finset.range k, (m + i) ↔ ¬∃ m, n = 2 ^ m := by 
  by_cases h : ∃ m, n = 2 ^ m 
  · rcases h with ⟨r, hr⟩
    use 0 
    use 0 
    simp [hr]
    all_goals omega 
  · use 1 
    use n 
    simp [Finset.sum_range_succ]
    <;> try { tauto }