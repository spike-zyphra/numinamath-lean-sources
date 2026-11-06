import Mathlib

def isMagic (N : ℕ) := ∀ m, N ∣ m * 10 ^ (Nat.digits 10 N).length + N

theorem number_theory_307296 :
    Set.ncard {N | N < 130 ∧ isMagic N} = 9 := by
  have h : {N | N < 130 ∧ isMagic N} = 
          {1, 2, 5, 10, 20, 25, 50, 100, 125} := by
    ext N 
    simp only [isMagic, Set.mem_setOf_eq, Set.mem_insert_iff, 
      Set.mem_singleton_iff, and_imp]
    constructor
    · -- First prove if N < 130 and is magic, then N ∈ {1, ..., 125}
      intro h
      rcases h with ⟨hN, hM⟩
      interval_cases N <;> norm_num at hM ⊢ 
        <;> try { 
          specialize hM 1 
          norm_num at hM ⊢ 
          all_goals omega 
        }
        <;> try { 
          specialize hM 2 
          norm_num at hM ⊢ 
          all_goals omega 
        }
        <;> try { 
          specialize hM 3 
          norm_num at hM ⊢ 
          all_goals omega 
        }
    · -- Now prove the reverse: each of {1, ..., 125} is a magic number
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | 
          rfl)
      · constructor
        · norm_num
        · intro m
          have h1 : (1 : ℕ) ∣ m * 10 ^ 1 + 1 := by 
            omega 
          simpa using h1 
      · constructor
        · norm_num 
        · intro m 
          have h1 : (2 : ℕ) ∣ m * 10 ^ 1 + 2 := by 
            omega 
          simpa using h1 
      · constructor
        · norm_num 
        · intro m 
          have h1 : (5 : ℕ) ∣ m * 10 ^ 1 + 5 := by 
            omega 
          simpa using h1 
      · constructor
        · norm_num 
        · intro m 
          have h1 : (10 : ℕ) ∣ m * 10 ^ 2 + 10 := by 
            omega 
          simpa using h1 
      · constructor
        · norm_num 
        · intro m 
          have h1 : (20 : ℕ) ∣ m * 10 ^ 2 + 20 := by 
            omega 
          simpa using h1 
      · constructor
        · norm_num 
        · intro m 
          have h1 : (25 : ℕ) ∣ m * 10 ^ 2 + 25 := by 
            omega 
          simpa using h1 
      · constructor
        · norm_num 
        · intro m 
          have h1 : (50 : ℕ) ∣ m * 10 ^ 2 + 50 := by 
            omega 
          simpa using h1 
      · constructor
        · norm_num 
        · intro m 
          have h1 : (100 : ℕ) ∣ m * 10 ^ 3 + 100 := by 
            omega 
          simpa using h1 
      · constructor
        · norm_num 
        · intro m 
          have h1 : (125 : ℕ) ∣ m * 10 ^ 3 + 125 := by 
            omega 
          simpa using h1 
  rw [h]
  rw [Set.ncard_eq_toFinset_card']
  simp 
  <;> try { native_decide }
  all_goals try { aesop }