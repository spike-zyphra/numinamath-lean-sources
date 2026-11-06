import Mathlib

theorem number_theory_230000 :
    {n : ℕ | n % 2 = 1 ∧ n % 3 = 2 ∧ n % 4 = 3 ∧ n % 5 = 4 ∧ n % 6 = 5 ∧ n % 7 = 0} = 
    {n : ℕ | ∃ k : ℕ, n = 420 * k + 119} := by
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor 
  · -- Forward implication: if n satisfies the conditions, then n = 420k + 119 for some k.
    rintro ⟨h2, h3, h4, h5, h6, h7⟩
    have h1 : n % 60 = 59 := by
      omega
    have h8 : n % 420 = 119 := by 
      omega 
    refine ⟨n / 420, by omega⟩
  · -- Backward implication: if n = 420k + 119 for some k, then n satisfies the conditions.
    rintro ⟨k, hk⟩
    have h1 : n % 2 = 1 := by
      omega
    have h2 : n % 3 = 2 := by 
      omega
    have h3 : n % 4 = 3 := by
      omega
    have h4 : n % 5 = 4 := by 
      omega
    have h5 : n % 6 = 5 := by 
      omega 
    have h6 : n % 7 = 0 := by 
      omega 
    exact ⟨h1, h2, h3, h4, h5, h6⟩