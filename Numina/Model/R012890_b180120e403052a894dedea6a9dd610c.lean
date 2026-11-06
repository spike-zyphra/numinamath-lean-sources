import Mathlib

theorem number_theory_205016 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (n / 100) % 10 = n % 10 ∧ ∃ k, n = k^2} = 3 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (n / 100) % 10 = n % 10 ∧ ∃ k, n = k^2} = {121, 484, 676} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n in the left side, need to show in {121, 484, 676}
      rintro ⟨⟨hn1, hn2⟩, h2, ⟨k, rfl⟩⟩
      have h3 : k ≤ 31 := by
        nlinarith 
      have h4 : k ≥ 10 := by
        nlinarith 
      interval_cases k <;> norm_num at *
    · -- Assume n in {121, 484, 676}, need to be in the left side 
      rintro (rfl | rfl | rfl)
      · -- n = 121
        constructor 
        · -- Show that 121 is in range 100-999
          norm_num
        constructor 
        · -- Show that the hundreds digit is equal to units digit
          norm_num
        · -- Show that 121 is a perfect square
          use 11
          all_goals norm_num
      · -- n = 484
        constructor 
        · -- Show that 484 is in range 100-999
          norm_num
        constructor 
        · -- Show that the hundreds digit is equal to units digit
          norm_num
        · -- Show that 484 is a perfect square
          use 22
          all_goals norm_num
      · -- n = 676
        constructor 
        · -- Show that 676 is in range 100-999
          norm_num
        constructor 
        · -- Show that the hundreds digit is equal to units digit
          norm_num
        · -- Show that 676 is a perfect square
          use 26
          all_goals norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]