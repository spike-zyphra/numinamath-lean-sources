import Mathlib

theorem number_theory_22766 :
    Set.ncard {x : ℕ | 0 < x ∧ x ≤ 100 ∧ 64 * x ≡ 2 [MOD 66]} = 3 := by 
  have h1 : {x : ℕ | 0 < x ∧ x ≤ 100 ∧ 64 * x ≡ 2 [MOD 66]} = {32, 65, 98} := by
    ext n
    simp [Nat.ModEq]
    constructor 
    · -- Assume n in the left side 
      rintro ⟨hn1, hn2, h⟩ 
      interval_cases n <;> omega 
    · -- Assume n in the right side 
      rintro (rfl | rfl | rfl) 
      · -- n = 32 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num [Nat.ModEq] 
      · -- n = 65 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num [Nat.ModEq] 
      · -- n = 98 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num [Nat.ModEq] 
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]