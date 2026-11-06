import Mathlib

theorem algebra_132217 :
    {(x, y) : ℤ × ℤ | x ≠ 0 ∧ y ≠ 0 ∧ (1 / x : ℚ) + (1 / y : ℚ) = 1 / 7}.ncard = 5 := by
  have h1 : {(x, y) : ℤ × ℤ | x ≠ 0 ∧ y ≠ 0 ∧ (1 / x : ℚ) + (1 / y : ℚ) = 1 / 7} = {(-42, 6), (6, -42), (56, 8), (8, 56), (14, 14)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x, y) is a solution.
      rintro ⟨hx, hy, heq⟩
      have hfrac : (x: ℚ) ≠ 0 := by exact_mod_cast hx
      have hf : (y: ℚ) ≠ 0 := by exact_mod_cast hy
      have h1 : (x * (y: ℚ) ) = 7 * (x: ℚ) + 7 * (y: ℚ) := by 
        have eq1 : (1 / x + 1 / y : ℚ) = 1 / 7 := by
          have eq2 : (1 / x : ℚ) + (1 / y : ℚ) = (↑x)⁻¹ + (↑y)⁻¹ := by 
            simp [hfrac, hf]
          have eq3 : (1 / x + 1 / y : ℚ) = (1 / 7 : ℚ) := by 
            rw [eq2]
            rw [heq]
            all_goals norm_num
          linarith
        have eq2 : (x * (y: ℚ) ) = 7 * (x: ℚ) + 7 * (y: ℚ) := by
          field_simp [hfrac, hf] at eq1 ⊢
          linarith
        linarith
      have h2 : (x * y : ℤ) = 7 * x + 7 * y := by 
        exact_mod_cast h1
      have h3 : (x - 7) * (y - 7) = 49 := by 
        nlinarith [h2]
      have h4 : x - 7 ∣ 49 := by
        use y - 7
        all_goals linarith [h3]
      have h5 : x - 7 ≤ 49 := by 
        apply Int.le_of_dvd (by norm_num) h4
      have h7 : x - 7 ≥ -49 := by 
        have h7 : (- (x - 7)) ∣ 49 := by 
          exact Int.neg_dvd.2 h4
        have h8 : - (x - 7) ≤ 49 := by 
          apply Int.le_of_dvd (by norm_num) h7
        omega
      interval_cases h : x - 7 <;> omega
    · -- Show that each pair in the right side set is a solution.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- pair (-42, 6)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- pair (6, -42)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- pair (56, 8)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- pair (8, 56)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- pair (14, 14)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }