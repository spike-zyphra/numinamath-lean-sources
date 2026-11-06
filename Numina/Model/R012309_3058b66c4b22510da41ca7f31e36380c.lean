import Mathlib

theorem algebra_20323 :
    {x : ℤ | ∃ a₁ a₂ a₃ : ℤ, x ^ 4 + a₃ * x ^ 3 + a₂ * x ^ 2 + a₁ * x + 4 = 0} = {-4, -2, -1, 1, 2, 4} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Show the polynomial can be written with integer coefficients 
    rintro ⟨a₁, a₂, a₃, h⟩
    have h1 : x ∣ 4 := by
      have h2 : x ∣ x ^ 4 := by
        use x ^ 3
        ring 
      have h3 : x ∣ (x ^ 4 + 4) := by
        have h_eq : x ^ 4 + 4 = - (a₃ * x ^ 3 + a₂ * x ^ 2 + a₁ * x) := by linarith 
        rw [h_eq]
        use - (a₃ * x ^ 2 + a₂ * x + a₁)
        all_goals nlinarith
      have h4 : x ∣ 4 := by 
        have h5 : x ∣ x ^ 4 := h2 
        have h6 : x ∣ (x ^ 4 + 4 - x ^ 4) := by
          apply Dvd.dvd.sub 
          · exact h3 
          · exact h5 
        have h7 : (x ^ 4 + 4 - x ^ 4) = 4 := by 
          nlinarith 
        rw [h7] at h6 
        exact h6 
      exact h4
    have h2 : x ∣ 4 := h1 
    have h3 : x ≤ 4 := by 
      exact Int.le_of_dvd (by norm_num) h2 
    have h4 : x ≥ -4 := by 
      have h5 : -x ∣ 4 := by 
        exact Int.neg_dvd.2 h2 
      have h6 : -x ≤ 4 := by 
        exact Int.le_of_dvd (by norm_num) h5 
      linarith 
    interval_cases x <;> omega 
  · -- Show the 2 direction, { -4, -2, -1, 1, 2, 4 } ⊆ {x | ∃ a₁ a₂ a₃ : ℤ, x ^ 4 + a₃ * x ^ 3 + a₂ * x ^ 2 + a₁ * x + 4 = 0}
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · -- Case x = -4 
      use 65, 0, 0 
      norm_num 
    · -- Case x = -2 
      use 10, 0, 0 
      norm_num 
    · -- Case x = -1 
      use 1, 0, 4 
      norm_num 
    · -- Case x = 1 
      use -5, 0, 0 
      norm_num 
    · -- Case x = 2 
      use -10, 0, 0 
      norm_num 
    · -- Case x = 4 
      use -65, 0, 0 
      norm_num