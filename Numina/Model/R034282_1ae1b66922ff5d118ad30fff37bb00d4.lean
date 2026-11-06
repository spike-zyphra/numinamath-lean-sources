import Mathlib

theorem number_theory_629350 : Set.ncard {x : ℕ | 0 < x ∧ (2019 / x : ℚ)
    ∈ Set.Ioo 0 2019 ∧ ∃ k : ℤ, 2019 / (x : ℚ) = k} = 3 := by 
  have h1 : {x : ℕ | 0 < x ∧ (2019 / x : ℚ)
      ∈ Set.Ioo 0 2019 ∧ ∃ k : ℤ, 2019 / (x : ℚ) = k} = {3, 673, 2019} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume h
      intro h
      rcases h with ⟨hx1, h2, ⟨k, hk⟩⟩
      rcases h2 with ⟨h3, h4⟩
      have h5 : (0 : ℚ) < (2019 / x : ℚ) := by
        simpa using h3
      have h6 : (2019 / x : ℚ) < (2019 : ℚ) := by
        simpa using h4
      have h7 : 0 < (2019 : ℚ) / (x : ℚ) := by 
        simpa using h5
      have h8 : (2019 : ℚ) / (x : ℚ) < (2019 : ℚ) := by
        simpa using h6
      have hx10 : x > 0 := by linarith
      have h11 : (0 : ℚ) < (2019 : ℚ) / (x : ℚ) := by linarith
      have h12 : (2019 : ℚ) / (x : ℚ) < (2019 : ℚ) := by linarith
      have h13 : (1 : ℚ) < (x : ℚ) := by
        have h10 : (2019 : ℚ) / (x : ℚ) < (2019 : ℚ) := h12
        have hx_pos : (x : ℚ) > 0 := by positivity
        apply (div_lt_iff₀ hx_pos).mp at h10 
        have h12' : (2019 : ℚ) < (2019 : ℚ) * (x : ℚ) := by nlinarith
        nlinarith
      have h14 : (2019 : ℚ) = (k : ℚ) * (x : ℚ) := by
        have h13' : (2019 / (x : ℚ) : ℚ) = (k : ℚ) := by
          simpa using hk
        have hx15 : (x : ℚ) ≠ 0 := by positivity
        field_simp at h13' ⊢
        nlinarith
      have h15 : (2019 : ℤ) = k * (x : ℤ) := by
        have h16 : (2019 : ℚ) = (k : ℚ) * (x : ℚ) := h14
        exact_mod_cast h16
      have h16 : (k : ℤ) ∣ (2019 : ℤ) := by
        use (x : ℤ)
        all_goals 
          linarith
      have h17 : k > 0 := by
        by_contra h
        push_neg at h
        have h18 : k ≤ 0 := by omega
        have h18' : (k : ℚ) ≤ 0 := by exact_mod_cast h18
        have h19 : (0 : ℚ) < (k : ℚ) := by
          have h13' : (2019 / (x : ℚ) : ℚ) = (k : ℚ) := by
            simpa using hk
          nlinarith [h5]
        nlinarith
      have h18 : k < 2019 := by
        have h18 : (k : ℚ) < (2019 : ℚ) := by
          have h40 : (2019 / x : ℚ) < (2019 : ℚ) := h12
          nlinarith [hk]
        exact_mod_cast h18
      have h19 : k = 1 ∨ k = 3 ∨ k = 673 := by
        have h20 : k > 0 := h17
        have h21 : k < 2019 := h18
        have h22 : k ∣ 2019 := by
          exact h16
        have h23 : k = 1 ∨ k = 3 ∨ k = 673 := by
          have h26 : k ≤ 2019 := by
            exact Int.le_of_dvd (by linarith) h22
          interval_cases k <;> norm_num at h22 h20 h21 ⊢ 
          <;> omega
        tauto
      rcases h19 with (r | r | r)
      · -- k = 1
        have hk1 : k = 1 := by linarith
        have hx2019 : x = 2019 := by
          rw [show (k : ℤ) = 1 by linarith] at h15
          omega
        rw [hx2019] 
        all_goals
          simp
      · -- k = 3
        have hk3 : k = 3 := by linarith
        have hx673 : x = 673 := by
          rw [show (k : ℤ) = 3 by linarith] at h15
          omega
        rw [hx673] 
        all_goals
          simp
      · -- k = 673
        have hk673 : k = 673 := by linarith
        have hx3 : x = 3 := by
          rw [show (k : ℤ) = 673 by linarith] at h15
          omega
        rw [hx3] 
        all_goals
          simp
    · -- Assume x ∈ {3, 673, 2019}, prove x ∈ {x : ℕ | 0 < x ∧ (2019 / x : ℚ) ∈ Set.Ioo 0 2019 ∧ ∃ k : ℤ, 2019 / (x : ℚ) = k}
      rintro (rfl | rfl | rfl)
      · -- x = 3
        constructor
        · norm_num
        constructor
        · norm_num [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        · use 673
          norm_num
      · -- x = 673
        constructor
        · norm_num
        constructor
        · norm_num [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        · use 3
          norm_num
      · -- x = 2019
        constructor
        · norm_num
        constructor
        · norm_num [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        · use 1
          norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp