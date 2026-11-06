import Mathlib

theorem number_theory_8256 : ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ Nat.Coprime a b ∧
    (a / b : ℚ) = {x | 3 ∣ x ∧ x ∣ 2007}.ncard / {x | x ∣ 2007}.ncard := by
  use 2, 3
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · -- Show that 2/3 = { {x | 3 divides x and x divides 2007} } / { {x | x divides 2007} }
    have h1 : {x | 3 ∣ x ∧ x ∣ 2007} = {3, 9, 669, 2007} := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · -- Assume h: 3 ∣ n ∧ n ∣ 2007
        rintro ⟨h3, hn⟩
        have h4 : n ≤ 2007 := by
          exact Nat.le_of_dvd (by norm_num) hn
        interval_cases n <;> norm_num at h3 hn ⊢ <;> tauto
      · -- Assume n ∈ {3, 9, 669, 2007}, prove 3 ∣ n ∧ n ∣ 2007
        rintro (rfl | rfl | rfl | rfl)
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
    have h2 : {x | x ∣ 2007} = {1, 3, 9, 223, 669, 2007} := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · -- Assume h: n ∣ 2007
        intro hn
        have h4 : n ≤ 2007 := by
          exact Nat.le_of_dvd (by norm_num) hn
        interval_cases n <;> norm_num at hn ⊢ <;> tauto
      · -- Assume n in the right side
        rintro (rfl | rfl | rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
    rw [h1]
    rw [h2]
    norm_num