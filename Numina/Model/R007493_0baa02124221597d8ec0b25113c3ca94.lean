import Mathlib

theorem number_theory_12241 :
    Set.ncard {n : ℕ | Odd n ∧ n ∣ 180} = 6 := by
  have h1 : {n : ℕ | Odd n ∧ n ∣ 180} = {1, 3, 5, 9, 15, 45} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Nat.odd_iff]
    constructor
    · -- Assume n is odd and divides 180
      intro h
      rcases h with ⟨hOdd, hDiv⟩
      have h2 : n ≤ 180 := by exact Nat.le_of_dvd (by norm_num) hDiv
      interval_cases n <;> norm_num at *
      <;> try { tauto }
    · -- Show that these numbers are odd and divide 180
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals native_decide