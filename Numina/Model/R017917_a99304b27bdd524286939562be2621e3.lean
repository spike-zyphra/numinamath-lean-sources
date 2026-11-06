import Mathlib

def isSquareFree (n : ℕ) := ∀ m, m^2 ∣ n → m = 1 ∨ m = n

theorem number_theory_7742 :
    Set.ncard {n | 90 ≤ n ∧ n ≤ 100 ∧ isSquareFree n} = 5 := by

  have h1 : {n | 90 ≤ n ∧ n ≤ 100 ∧ isSquareFree n} = {91, 93, 94, 95, 97} := by
    ext n
    simp [isSquareFree]
    constructor
    · -- First prove that if n is in the set, then n ∈ {91, 93, 94, 95, 97}
      intro hn
      rcases hn with ⟨h90, h100, hsf⟩
      interval_cases n <;> norm_num at *
      <;> try { tauto }
      <;> try { 
        exfalso
        have h2 : 3^2 ∣ 90 := by norm_num 
        have := hsf 3 h2
        norm_num at this 
      }
      <;> try { 
        exfalso
        have h2 : 2^2 ∣ 92 := by norm_num 
        have := hsf 2 h2 
        norm_num at this 
      }
      <;> try { 
        exfalso
        have h2 : 4^2 ∣ 96 := by norm_num 
        have := hsf 4 h2 
        norm_num at this 
      }
      <;> try { 
        exfalso
        have h2 : 7^2 ∣ 98 := by norm_num 
        have := hsf 7 h2 
        norm_num at this 
      }
      <;> try { 
        exfalso
        have h2 : 3^2 ∣ 99 := by norm_num 
        have := hsf 3 h2 
        norm_num at this 
      }
      <;> try { 
        exfalso 
        have h2 : 10^2 ∣ 100 := by norm_num 
        have := hsf 10 h2 
        norm_num at this 
      }
      <;> try { 
        exfalso 
        have h2 : 2^2 ∣ (96 : ℕ) := by norm_num 
        have := hsf 2 h2 
        norm_num at this 
      }
      <;> try { 
        exfalso 
        have h2 : 2^2 ∣ (96 : ℕ) := by norm_num 
        have := hsf 2 h2 
        norm_num at this 
      }
      
    
    · -- Show that the entries in {91, 93, 94, 95, 97} are squarefree
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- Show 91 is square-free
        constructor
        · norm_num
        constructor
        · norm_num 
        · intro m h
          have h1 : m ≤ 31 := by
            have h30 : m^2 ∣ 91 := h
            have h31 : m^2 ≤ 91 := by
              exact Nat.le_of_dvd (by norm_num) h30
            have h32 : m ≤ 31 := by
              nlinarith
            exact h32
          interval_cases m <;> norm_num at h ⊢ <;> try { tauto }
      · -- Show 93 is square-free
        constructor
        · norm_num
        constructor
        · norm_num 
        · intro m h
          have h1 : m ≤ 30 := by
            have h30 : m^2 ∣ 93 := h
            have h31 : m^2 ≤ 93 := by
              exact Nat.le_of_dvd (by norm_num) h30
            have h32 : m ≤ 30 := by
              nlinarith
            exact h32
          interval_cases m <;> norm_num at h ⊢ <;> try { tauto }
      · -- Show 94 is square-free
        constructor
        · norm_num
        constructor
        · norm_num 
        · intro m h
          have h1 : m ≤ 30 := by
            have h30 : m^2 ∣ 94 := h
            have h31 : m^2 ≤ 94 := by
              exact Nat.le_of_dvd (by norm_num) h30
            have h32 : m ≤ 30 := by
              nlinarith
            exact h32
          interval_cases m <;> norm_num at h ⊢ <;> try { tauto }
      · -- Show 95 is square-free
        constructor
        · norm_num
        constructor
        · norm_num 
        · intro m h
          have h1 : m ≤ 30 := by
            have h30 : m^2 ∣ 95 := h
            have h31 : m^2 ≤ 95 := by
              exact Nat.le_of_dvd (by norm_num) h30
            have h32 : m ≤ 30 := by
              nlinarith
            exact h32
          interval_cases m <;> norm_num at h ⊢ <;> try { tauto }
      · -- Show 97 is square-free
        constructor
        · norm_num
        constructor
        · norm_num 
        · intro m h
          have h1 : m ≤ 31 := by
            have h30 : m^2 ∣ 97 := h
            have h31 : m^2 ≤ 97 := by
              exact Nat.le_of_dvd (by norm_num) h30
            have h32 : m ≤ 31 := by
              nlinarith
            exact h32
          interval_cases m <;> norm_num at h ⊢ <;> try { tauto }
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]