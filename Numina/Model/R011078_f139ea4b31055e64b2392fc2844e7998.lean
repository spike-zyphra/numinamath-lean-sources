import Mathlib


theorem algebra_220023 : {(x, y) : ℤ × ℤ | x ≠ 0 ∧ y ≠ 0 ∧ (1 / x : ℚ) +
    (1 / y : ℚ) = 1 / 7}.ncard = 5 := by
  have h1 : {(x, y) : ℤ × ℤ | x ≠ 0 ∧ y ≠ 0 ∧ (1 / x : ℚ) +
      (1 / y : ℚ) = 1 / 7} = {(-42, 6), (6, -42), (14, 14), (8, 56), (56, 8)} := by 
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume h hold.
      rintro ⟨hx, hy, heq⟩
      have h_eq : (x: ℚ) * (y: ℚ) = 7 * (x: ℚ) + 7 * (y: ℚ) := by 
        field_simp at heq ⊢
        linarith
      have h_eq2 : (x: ℤ) * (y: ℤ) = 7 * (x: ℤ) + 7 * (y: ℤ) := by 
        exact_mod_cast h_eq 
      have h2 : (x - 7) * (y - 7) = 49 := by linarith [h_eq2]
      have h8 : (x - 7) ∣ 49 := by
        use (y - 7)
        all_goals linarith [h2]
      have h9 : (x - 7) = 1 ∨ (x - 7) = 7 ∨ (x - 7) = 49 ∨ (x - 7) = -1 ∨ (x - 7) = -7 ∨ (x - 7) = -49 := by
        have h8a : (x - 7) ∣ 49 := h8 
        have h10 : (x - 7) ∣ 49 := h8
        have h11 : (x - 7) ≤ 49 := by 
          apply Int.le_of_dvd (by norm_num) h10
        have h12 : (x - 7) ≥ -49 := by 
          have h7 : -(x - 7) ∣ 49 := by 
            exact Int.neg_dvd.2 h10
          have h8 : -(x - 7) ≤ 49 := by
            apply Int.le_of_dvd (by norm_num) h7
          omega 
        interval_cases k : (x - 7) <;> try { tauto }
      rcases h9 with (h | h | h | h | h | h)
      · -- x - 7 = 1 ⇒ x = 8 ⇒ y = 56 
        have hx' : x = 8 := by linarith 
        have hy' : y = 56 := by nlinarith 
        simp [hx', hy']
      · -- x - 7 = 7 ⇒ x = 14 ⇒ y = 14 
        have hx' : x = 14 := by linarith 
        have hy' : y = 14 := by nlinarith 
        simp [hx', hy']
      · -- x - 7 = 49 ⇒ x = 56 ⇒ y = 8 
        have hx' : x = 56 := by linarith 
        have hy' : y = 8 := by nlinarith 
        simp [hx', hy']
      · -- x - 7 = -1 ⇒ x = 6 ⇒ y = -42 
        have hx' : x = 6 := by linarith 
        have hy' : y = -42 := by nlinarith 
        simp [hx', hy']
      · -- x - 7 = -7 ⇒ x = 0 
        have hx' : x = 0 := by linarith 
        exfalso 
        apply hx 
        all_goals linarith 
      · -- x - 7 = -49 ⇒ x = -42 ⇒ y = 6 
        have hx' : x = -42 := by linarith 
        have hy' : y = 6 := by nlinarith 
        simp [hx', hy']
    · -- Show that these are valid.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (-42, 6)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (6, -42)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (14, 14)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (8, 56)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (56, 8)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try native_decide