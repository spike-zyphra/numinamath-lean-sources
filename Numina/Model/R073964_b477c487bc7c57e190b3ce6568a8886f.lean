import Mathlib

theorem number_theory_98443 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n + (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = 132} = 7 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n + (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = 132} = {39,48,57,66,75,84,93} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n is in the left side, prove n is in the right side
      intro h
      rcases h with ⟨⟨hn1, hn2⟩, hneq⟩
      interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at hneq ⊢ <;> omega
    · -- Assume n is in the right side, prove it is in the left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 39
        constructor
        · -- Show that 39 is in [10, 99]
          native_decide
        · -- Show that 39 + reverse(39) = 132
          native_decide
      · -- n = 48
        constructor
        · -- Show that 48 is in [10, 99]
          native_decide
        · -- Show that 48 + reverse(48) = 132
          native_decide
      · -- n = 57
        constructor
        · -- Show that 57 is in [10, 99]
          native_decide
        · -- Show that 57 + reverse(57) = 132
          native_decide
      · -- n = 66
        constructor
        · -- Show that 66 is in [10, 99]
          native_decide
        · -- Show that 66 + reverse(66) = 132
          native_decide
      · -- n = 75
        constructor
        · -- Show that 75 is in [10, 99]
          native_decide
        · -- Show that 75 + reverse(75) = 132
          native_decide
      · -- n = 84
        constructor
        · -- Show that 84 is in [10, 99]
          native_decide
        · -- Show that 84 + reverse(84) = 132
          native_decide
      · -- n = 93
        constructor
        · -- Show that 93 is in [10, 99]
          native_decide
        · -- Show that 93 + reverse(93) = 132
          native_decide
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]