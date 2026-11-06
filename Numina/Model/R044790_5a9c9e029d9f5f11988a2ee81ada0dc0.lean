import Mathlib

def is_in_list (n : ℕ) := ∃ p, p.Prime ∧ p % 10 = n

theorem number_theory_235088 :
    {n | n ∈ Finset.Icc 1 5 ∧ is_in_list n}.encard = 4 := by 
  have h1 : {n | n ∈ Finset.Icc 1 5 ∧ is_in_list n} = {1, 2, 3, 5} := by
    ext n 
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n in {n ∈ [1, 5] ∧ ∃ prime p, p % 10 = n}
      rintro ⟨⟨hn1, hn2⟩, ⟨p, hp, hpu⟩⟩ 
      have h2 : n ≤ 5 := by linarith
      have h3 : n ≥ 1 := by linarith 
      interval_cases n <;> try { 
        try { 
          tauto 
        } 
        <;> try { 
          have h4 : p % 10 = 4 := by 
            omega 
          -- Show that this leads to a contradiction.
          have h6 : p % 2 = 0 := by 
            omega 
          have h7 : p = 2 := by
            by_cases h8 : p > 2 
            · -- Assume p > 2 
              have h9 : p % 2 = 0 := h6 
              have h11 : p > 1 := by 
                omega 
              have h13 : ¬p.Prime := by 
                apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by 
                  omega 
                ) 
                all_goals 
                omega 
              contradiction 
            · -- Assume p ≤ 2 
              have h8 : p ≤ 2 := by 
                omega 
              interval_cases p <;> norm_num at hp h4 
          omega 
        }
      }
    · -- Assume n in {1, 2, 3, 5}, prove it in {n ∈ [1, 5] ∧ ∃ prime p, p % 10 = n}
      rintro (h | h | h | h)
      · -- n = 1
        rw [show n = 1 by tauto]
        constructor 
        · 
          native_decide 
        · -- Show that ∃p, p prime ∧ p % 10 = 1 
          use 11
          all_goals norm_num
      · -- n = 2
        rw [show n = 2 by tauto]
        constructor 
        · 
          native_decide 
        · -- Show that ∃p, p prime ∧ p % 10 = 2 
          use 2 
          all_goals norm_num
      · -- n = 3 
        rw [show n = 3 by tauto]
        constructor 
        · 
          native_decide 
        · -- Show that ∃p, p prime ∧ p % 10 = 3
          use 3 
          all_goals norm_num
      · -- n = 5 
        rw [show n = 5 by tauto]
        constructor 
        · 
          native_decide 
        · -- Show that ∃p, p prime ∧ p % 10 = 5 
          use 5 
          all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try native_decide