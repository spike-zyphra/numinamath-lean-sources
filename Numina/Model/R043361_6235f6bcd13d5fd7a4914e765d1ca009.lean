import Mathlib

def a (n : ℕ) := n ^ 2 + n + 2

theorem number_theory_308259 :
    Set.Finite {n | ∃ m, a n = m ^ 2} := by
  have h1 : {n | ∃ m, a n = m ^ 2} = {1} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, a]
    constructor
    · -- Assume that exists m, a n = m^2, need to prove n =1
      intro h
      rcases h with ⟨m, hm⟩
      by_cases h2 : m > n + 1
      · -- Assume m > n + 1
        have h3 : m ≤ n + 2 := by
          nlinarith [sq_nonneg ((m : ℤ) - (n + 1 : ℤ)), sq_nonneg ((m : ℤ) + (n + 1 : ℤ)), 
            sq_nonneg (m ^ 2 - (n ^ 2 + n + 2 : ℤ)), 
            sq_nonneg (m - (n + 1 : ℤ)), sq_nonneg (m + (n + 1 : ℤ))
          ]
        have h4 : n ≤ 2 := by
          nlinarith [sq_nonneg ((m : ℤ) - (n + 1 : ℤ)), sq_nonneg ((m : ℤ) + (n + 1 : ℤ)), 
            sq_nonneg (m ^ 2 - (n ^ 2 + n + 2 : ℤ)), 
            sq_nonneg (m - (n + 1 : ℤ)), sq_nonneg (m + (n + 1 : ℤ))
          ]
        interval_cases n <;> try { 
          norm_num at hm
          all_goals
          have h4 : m ≤ 4 := by 
            nlinarith
          interval_cases m <;> all_goals
          omega
        }
      · -- Assume m ≤ n + 1
        by_cases h3 : m < n + 1
        · -- Assume m < n + 1
          nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ)), sq_nonneg ((m : ℤ) + (n + 1 : ℤ)), 
            sq_nonneg (m ^ 2 - (n ^ 2 + n + 2 : ℤ)), 
            sq_nonneg (m - (n + 1 : ℤ)), sq_nonneg (m + (n + 1 : ℤ))
          ]
        · -- Assume m = n + 1
          have h4 : m = n + 1 := by 
            omega
          rw [h4] at hm
          nlinarith
    · -- Assume n =1, need to prove exists m, a 1 = m^2
      intro h
      rw [h]
      use 2
      all_goals
      norm_num [a]
  rw [h1]
  simp
  <;> try { tauto }