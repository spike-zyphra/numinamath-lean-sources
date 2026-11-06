import Mathlib

theorem number_theory_128021 : {n : ℕ | ∃ k, n = k^2 ∧ n ∣ 1600}.encard = 8 := by
  have h1 : {n : ℕ | ∃ k, n = k^2 ∧ n ∣ 1600} = {1, 4, 16, 25, 64, 100, 400, 1600} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n is in the left side
      rintro ⟨k, rfl, hk⟩
      have h30 : k^2 ≤ 1600 := by
        exact Nat.le_of_dvd (show (0 : ℕ) < (1600 : ℕ) by norm_num) hk
      have h31 : k ≤ 40 := by
        nlinarith [sq_nonneg (k: ℕ), sq_nonneg ((40 : ℕ) - k), sq_nonneg ((k: ℝ) - (40 : ℝ)), h30]
      interval_cases k <;> norm_num at *
      <;> tauto
      <;> nlinarith
      <;> try { contradiction }
    · -- Assume n is on the right side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show 1 is in the left side
        use 1
        all_goals norm_num
      · -- Show 4 is in the left side
        use 2
        all_goals norm_num
      · -- Show 16 is in the left side
        use 4
        all_goals norm_num
      · -- Show 25 is in the left side
        use 5
        all_goals norm_num
      · -- Show 64 is in the left side
        use 8
        all_goals norm_num
      · -- Show 100 is in the left side
        use 10
        all_goals norm_num
      · -- Show 400 is in the left side
        use 20
        all_goals norm_num
      · -- Show 1600 is in the left side
        use 40
        all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }