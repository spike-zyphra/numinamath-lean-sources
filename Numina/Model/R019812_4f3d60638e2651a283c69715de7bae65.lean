import Mathlib

theorem algebra_4860 : ∑ᶠ (a : ℤ) (_ : ∃ (b : ℤ), (a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + 1 / b = 2 / 7)), a = 39 := by
  have h1 : {a : ℤ | ∃ (b : ℤ), (a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + 1 / b = 2 / 7)} = {4, 7, 28} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First, prove if $a$ is in the set, then $a \in \{ 4, 7, 28 \}$.
      rintro ⟨b, ⟨ha, hb, heq⟩⟩
      have h1 : (a : ℚ) > 0 := by exact_mod_cast ha
      have h2 : (b : ℚ) > 0 := by exact_mod_cast hb
      have h3 : (1 / a : ℚ) + (1 / b : ℚ) = (2 / 7 : ℚ) := heq
      have eq1 : 2 * (a * (b : ℤ)) = 7 * (a + b) := by
        field_simp at h3
        have eq1 : (2 * (a * (b : ℚ)) = 7 * (a + b : ℚ)) := by
          linarith
        exact_mod_cast eq1
      have eq3 : (2 * a - 7) * (2 * b - 7) = 49 := by
        nlinarith 
      have h4 : (2 * a - 7) ∣ 49 := by
        use 2 * b - 7 
        all_goals linarith
      have h6 : (2 * a - 7) ≥ -49 := by
        have h7 : (- (2 * a - 7) ) ∣ 49 := by
          exact Int.neg_dvd.2 h4
        have h8 : (- (2 * a - 7) ) ≤ 49 := by
          apply Int.le_of_dvd (by norm_num) h7
        omega
      have h7 : (2 * a - 7) ≤ 49 := by
        apply Int.le_of_dvd (by norm_num) h4
      interval_cases h : (2 * a - 7) <;> omega
    · -- Now prove the reverse: if $a \in \{4, 7, 28\}$, then $a$ is in the set
      rintro (rfl | rfl | rfl)
      · -- Case a = 4, b = 28
        use 28
        norm_num
      · -- Case a = 7, b = 7
        use 7
        norm_num
      · -- Case a = 28, b = 4
        use 4
        norm_num
  rw [show ∑ᶠ (a : ℤ) (_ : ∃ (b : ℤ), (a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + 1 / b = 2 / 7)), a = ∑ᶠ (a ∈ {a : ℤ | ∃ (b : ℤ), (a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + 1 / b = 2 / 7)}), a by simp]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> try native_decide