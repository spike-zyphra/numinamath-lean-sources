import Mathlib

theorem algebra_6403 :
  ∑ᶠ x ∈ {x : ℕ | ∃ y : ℕ, 0 < x ∧ 0 < y ∧ (1/7 : ℚ) = 1/x + 1/y}, x = 78 := by
  have h1 : {x : ℕ | ∃ y : ℕ, 0 < x ∧ 0 < y ∧ (1/7 : ℚ) = 1/x + 1/y} = {8, 14, 56} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in the set
      intro h
      rcases h with ⟨y, hx1, hy1, heq⟩
      have h2 : (x : ℚ) > 0 := by exact_mod_cast hx1
      have h3 : (y : ℚ) > 0 := by exact_mod_cast hy1
      have h4 : (x : ℚ) * (y : ℚ) = 7 * ((x : ℚ) + (y : ℚ)) := by
        field_simp at heq
        nlinarith
      have h5 : (x : ℤ) * (y : ℤ) = 7 * ((x : ℤ) + (y : ℤ)) := by
        exact_mod_cast h4
      have h7 : ((x : ℤ) - 7) * ((y : ℤ) - 7) = 49 := by
        nlinarith
      have h12 : (x : ℤ) - 7 = 1 ∨ (x : ℤ) - 7 = 7 ∨ (x : ℤ) - 7 = 49 ∨ (x : ℤ) - 7 = -1 ∨ (x : ℤ) - 7 = -7 ∨ (x : ℤ) - 7 = -49 := by
        have h9 : (x : ℤ) - 7 ∣ 49 := by
          use (y : ℤ) - 7
          linarith
        have h12 : (x : ℤ) - 7 ∣ 49 := h9
        have h14 : (x : ℤ) - 7 ≤ 49 := by
          apply Int.le_of_dvd (by norm_num) h9
        have h15 : (x : ℤ) - 7 ≥ -49 := by
          have h15 : -( (x : ℤ) - 7 ) ∣ 49 := by
            exact Int.neg_dvd.2 h9
          have h16 : -( (x : ℤ) - 7 ) ≤ 49 := by
            apply Int.le_of_dvd (by norm_num) h15
          linarith
        interval_cases (x : ℤ) - 7 <;> tauto
      rcases h12 with h12 | h12 | h12 | h12 | h12 | h12
      · -- x - 7 = 1, so x = 8
        have hx2 : (x : ℤ) = 8 := by
          linarith
        have hx3 : x = 8 := by
          exact_mod_cast hx2
        simp [hx3]
        <;> omega
      · -- x - 7 = 7, so x = 14
        have hx2 : (x : ℤ) = 14 := by
          linarith
        have hx3 : x = 14 := by
          exact_mod_cast hx2
        simp [hx3]
        <;> omega
      · -- x - 7 = 49, so x = 56
        have hx2 : (x : ℤ) = 56 := by
          linarith
        have hx3 : x = 56 := by
          exact_mod_cast hx2
        simp [hx3]
        <;> omega
      · -- x - 7 = -1, so x = 6
        have hx2 : (x : ℤ) = 6 := by
          linarith
        have hx3 : x = 6 := by
          exact_mod_cast hx2
        have eq1 : (y : ℤ) = -42 := by
          rw [show (x : ℤ) = 6 from hx2] at h5
          omega
        have eq2 : (y : ℤ) ≥ 0 := by
          have : (y : ℤ) ≥ 0 := by
            omega 
          linarith
        omega -- contradicts eq1 
      · -- x - 7 = -7, so x = 0
        have hx2 : (x : ℤ) = 0 := by
          linarith
        have hx3 : x = 0 := by
          exact_mod_cast hx2
        omega -- contradicts hx1
      · -- x - 7 = -49, so x = -42
        exfalso
        have hx2 : (x : ℤ) = -42 := by
          linarith
        have hx3 : x = 0 := by
          omega 
        omega
    · -- Assume x ∈ {8, 14, 56}
      rintro (rfl | rfl | rfl)
      · -- x = 8
        use 56
        all_goals norm_num
      · -- x = 14
        use 14
        all_goals norm_num
      · -- x = 56
        use 8
        all_goals norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> norm_num
  all_goals
    try tauto
    <;> norm_num
    <;> tauto