import Mathlib

theorem algebra_97271 : {k : ℕ | ∃ x : ℤ, k * x - 12 = 3 * k}.encard = 6 := by
  have h1 : {k : ℕ | ∃ x : ℤ, k * x - 12 = 3 * k} = {1, 2, 3, 4, 6, 12} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume k and some integer x satisfy k * x - 12 = 3 * k
      rintro ⟨x, hx⟩
      have h2 : (k : ℤ) * x = 3 * (k : ℤ) + 12 := by 
        linarith
      have h3 : (k : ℤ) ≠ 0 := by
        by_contra h
        rw [h] at h2
        omega
      have h4 : (k : ℤ) ∣ 12 := by
        use (x - 3)
        linarith
      have h5 : k ∣ 12 := by 
        have hk12 : (k : ℤ) ∣ 12 := h4
        have : k ∣ 12 := by
          exact_mod_cast hk12
        exact this
      have h6 : k ≤ 12 := by 
        exact Nat.le_of_dvd (by norm_num) h5
      interval_cases k <;> 
        try { tauto }
        <;> omega
    · -- Show that these six possible k's satisfy the equation
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- k = 1 
        use 15
        all_goals omega
      · -- k = 2
        use 9
        all_goals omega
      · -- k = 3
        use 7
        all_goals omega
      · -- k = 4
        use 6
        all_goals omega
      · -- k = 6
        use 5
        all_goals omega
      · -- k = 12
        use 4
        all_goals omega
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { trivial }
  all_goals omega