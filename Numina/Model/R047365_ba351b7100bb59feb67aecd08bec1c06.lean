import Mathlib

theorem algebra_175319 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a < b ∧ (1 / a : ℚ) + (1 / b : ℚ) = 4 / 15}.ncard = 3 := by
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a < b ∧ (1 / a : ℚ) + (1 / b : ℚ) = 4 / 15} = {(6, 10), (5, 15), (4, 60)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Assume ⟨a, b⟩ is in the set, prove it must be one of the pairs
      rintro ⟨ha, hb, hab, heq⟩
      have h_eq : (a : ℚ) > 0 := by exact_mod_cast ha
      have h_eq' : (b : ℚ) > 0 := by exact_mod_cast hb
      have eq1 : (a : ℚ) * (b : ℚ) = (15 / 4) * (a + b) := by
        field_simp at heq ⊢
        nlinarith
      have eq2 : 4 * (a : ℚ) * (b : ℚ) = 15 * (a + b) := by
        linarith [eq1]
      have eq3 : 4 * (a : ℕ) * (b : ℕ) = 15 * (a + b) := by
        exact_mod_cast eq2
      have h2 : a ≤ 60 := by
        by_contra h
        push_neg at h
        have h3 : b < 60 := by
          nlinarith [ sq_nonneg ( (4 : ℕ) * a - (15 : ℕ) ), sq_nonneg ( (4 : ℕ) * b - (15 : ℕ) ), mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (b : ℕ) by linarith) ]
        interval_cases b <;> omega
      have h3 : b ≤ 60 := by
        by_contra h
        push_neg at h
        have h4 : a < 60 := by
          nlinarith [ sq_nonneg ( (4 : ℕ) * a - (15 : ℕ) ), sq_nonneg ( (4 : ℕ) * b - (15 : ℕ) ), mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (b : ℕ) by linarith) ]
        interval_cases a <;> omega
      interval_cases a <;> omega
    · -- Show that each of { (6,10),(5,15),(4,60) } is in the set.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ )
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]