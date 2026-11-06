import Mathlib
/-How many pairs of positive integers (a,b) with ≤ b satisfy 1/a + 1/b = 1/6-/
theorem algebra_154295 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a ≤ b ∧ (1 / a : ℚ) + (1 / b : ℚ) = 1 / 6}.ncard = 5 := by
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a ≤ b ∧ (1 / a : ℚ) + (1 / b : ℚ) = 1 / 6} = {(7, 42), (8, 24), (9, 18), (10, 15), (12, 12)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Assume (a, b) satisfies the conditions
      rintro ⟨ha_pos, hb_pos, h_le, h_eq⟩
      have h_eq1 : (a : ℚ) > 0 := by exact_mod_cast ha_pos
      have h_eq2 : (b : ℚ) > 0 := by exact_mod_cast hb_pos
      have eq1 : (a : ℚ) * (b : ℚ) - 6 * (a : ℚ) - 6 * (b : ℚ) = 0 := by
        field_simp at h_eq
        nlinarith
      have eq2 : (a : ℤ) * (b : ℤ) - 6 * (a : ℤ) - 6 * (b : ℤ) = 0 := by
        qify at eq1 ⊢
        linarith
        -- we show that a is less than 13
      have h1 : a ≤ 12 := by
        by_contra h
        push_neg at h
        have h2 : (a : ℤ) > 12 := by norm_cast
        have h3 : (a : ℤ) - 6 > 6 := by linarith
        have h_eq : ((a : ℤ) - 6) * ((b : ℤ) - 6) = 36 := by
          nlinarith [eq2]
        have h4 : (b : ℤ) - 6 < 6 := by
          nlinarith [h3, h_eq]
        have h5 : (b : ℤ) < 12 := by linarith
        have h6 : a ≤ b := by exact_mod_cast h_le
        have h7 : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast h6
        linarith
      -- now check all cases 
      interval_cases a <;> 
      try { 
        omega 
      }
      
    · -- Show that each of the 5 pairs satisfies the conditions
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  norm_num