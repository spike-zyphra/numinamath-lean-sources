import Mathlib

theorem number_theory_232329 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ ∃ k, n = k^2 ∧ ∃ m, m^2 = (Nat.digits 10 n).prod} = 1 := by
  have h : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ ∃ k, n = k^2 ∧ ∃ m, m^2 = (Nat.digits 10 n).prod} = {49} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- First direction: if n is in the set, it's 49
      rintro ⟨⟨hn1, hn2⟩, k, hxn, m, hprod⟩
      have hk1 : k ≤ 9 := by
        by_contra h
        push_neg at h
        have h2 : k ^ 2 ≥ 100 := by
          have : k ≥ 10 := by linarith
          have h3 : k ^ 2 ≥ 100 := by
            nlinarith
          linarith [h3]
        have h2' : n ≥ 100 := by
          rw [hxn]
          nlinarith [h2]
        omega
      have hk2 : k ≥ 4 := by
        by_contra h
        push_neg at h
        have h2 : k ^ 2 ≤ 9 := by
          have : k ≤ 3 := by linarith
          have h3 : k ^ 2 ≤ 9 := by
            nlinarith
          linarith [h3]
        have h2' : n ≤ 9 := by
          rw [hxn]
          nlinarith [h2]
        omega
      interval_cases k <;> norm_num [hxn] at *
      all_goals
        try { 
          have h1 : m ≤ 31 := by
            by_contra h2
            push_neg at h2
            have h2' : m ^ 2 ≥ 1024 := by
              nlinarith [h2]
            omega
          interval_cases m <;> norm_num at hprod <;> omega 
        }
        <;> try { 
          all_goals
          omega 
        }
    · -- Second direction: 49 is in the set
      intro h1
      rw [h1]
      constructor
      · -- Show 49 ∈ [10, 99]
        simp
      · -- Show ∃k, 49 = k^2 ∧ ∃m, m^2 = (Nat.digits 10 49).prod
        use 7
        constructor
        · -- Show 49 = 7^2
          all_goals
            { 
              norm_num 
            }
        · -- Show ∃m, m^2 = (Nat.digits 10 49).prod
          use 6
          all_goals
            { 
              norm_num 
            }
  rw [h]
  simp