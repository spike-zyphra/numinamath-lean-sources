import Mathlib

def isMagic (N : ℕ) := ∀ m, N ∣ m * 10 ^ (Nat.digits 10 N).length + N

theorem number_theory_179248 :
    Set.ncard {N | N < 130 ∧ isMagic N} = 9 := by

  have h1 : {N | N < 130 ∧ isMagic N} = {1, 2, 5, 10, 20, 25, 50, 100, 125} := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, isMagic]
    constructor
    · -- Assume N < 130 and isMagic N, prove N ∈ {1, 2, 5, 10, 20, 25, 50, 100, 125}
      intro h
      rcases h with ⟨hN, hMagic⟩
      interval_cases N <;> try { tauto }
      <;> try { 
        exfalso
        have h1 := hMagic 1
        norm_num at h1 <;> omega 
      }
    · -- Assume N ∈ {1, 2, 5, 10, 20, 25, 50, 100, 125}, prove N < 130 ∧ isMagic N
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · intro m
          omega
      · constructor
        · norm_num
        · intro m
          norm_num
          all_goals omega
      · constructor
        · norm_num
        · intro m
          norm_num
          all_goals omega
      · constructor
        · norm_num
        · intro m
          norm_num
          all_goals omega
      · constructor
        · norm_num
        · intro m
          norm_num
          all_goals omega
      · constructor
        · norm_num
        · intro m
          norm_num
          all_goals omega
      · constructor
        · norm_num
        · intro m
          norm_num
          all_goals omega
      · constructor
        · norm_num
        · intro m
          norm_num
          all_goals omega
      · constructor
        · norm_num
        · intro m
          norm_num
          all_goals omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { tauto }