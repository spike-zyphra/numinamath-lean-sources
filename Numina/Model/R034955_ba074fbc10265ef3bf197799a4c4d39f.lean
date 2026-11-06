import Mathlib

theorem number_theory_13817 (n : ℕ) (hn : n = 100) :
    {p | p.Prime ∧ ∃ k, p = n - 5 * k}.encard ≤ 18 := by 
  rw [hn]
  have h : {p | p.Prime ∧ ∃ k, p = (100 : ℕ) - 5 * k} = {5} := by 
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume p is in the set
      intro hp
      rcases hp with ⟨h_prime, ⟨k, hk⟩⟩
      have h1 : p = 100 - 5 * k := by linarith
      have h2 : k ≤ 19 := by
        by_contra h
        push_neg at h
        have : 5 * k ≥ 100 := by 
          omega
        have h3 : (100 - 5 * k : ℕ) = 0 := by
          omega
        have hp' : p = 0 := by
          omega
        rw [hp'] at h_prime
        norm_num at h_prime
        all_goals try { tauto }
      interval_cases k <;> norm_num [h1] at *
      <;> tauto 
    · -- Assume p = 5 
      intro hp 
      rw [hp]
      constructor
      · norm_num 
      · use 19
        all_goals norm_num 
  rw [h]
  simp [Set.encard_singleton]
  all_goals
  try { tauto }
  try { linarith }