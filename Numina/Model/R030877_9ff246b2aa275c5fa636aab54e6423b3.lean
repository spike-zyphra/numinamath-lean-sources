import Mathlib

theorem algebra_4684 :
    {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ x * y + 20 * x - 18 * y = 110}.ncard = 4 := by
  have h1 : {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ x * y + 20 * x - 18 * y = 110} = 
    {(8, 5), (13, 30), (16, 105), (17, 230)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- First direction: if $(x,y)$ in the set, then it's in $\{(8,5),(13,30),(16,105),(17,230)\}$.
      rintro ⟨hx, hy, h⟩
      have h2 : x * (y + 20) = 18 * (y + 20) - 250 := by
        nlinarith
      have h3 : (x - 18) * (y + 20) = -250 := by
        nlinarith 
      have h10 : y + 20 ≥ 21 := by 
        omega 
      -- From h3, we know that $y + 20$ divides $250$.
      have h4 : y + 20 ∣ 250 := by
        use (18 - x)
        all_goals nlinarith 
      have h11 : y + 20 = 25 ∨ y + 20 = 50 ∨ y + 20 = 125 ∨ y + 20 = 250 := by
        have h12 : y + 20 ∣ 250 := h4
        have h13 : y + 20 ≥ 1 := by 
          omega 
        have h14 : y + 20 ≤ 250 := by
          exact Int.le_of_dvd (by norm_num) h12
        interval_cases k : y + 20 <;> tauto 
      rcases h11 with h7 | h7 | h7 | h7
      · -- Case 1
        have hy1 : y = 5 := by 
          omega 
        have hx1 : x = 8 := by
          nlinarith 
        simp [hx1, hy1]
      · -- Case 2
        have hy2 : y = 30 := by 
          omega 
        have hx2 : x = 13 := by
          nlinarith 
        simp [hx2, hy2]
      · -- Case 3
        have hy3 : y = 105 := by 
          omega 
        have hx3 : x = 16 := by
          nlinarith 
        simp [hx3, hy3]
      · -- Case 4
        have hy4 : y = 230 := by 
          omega 
        have hx4 : x = 17 := by
          nlinarith 
        simp [hx4, hy4]
    · -- Second direction: each in {(8, 5), (13, 30), (16, 105), (17, 230)} is in the set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (8, 5)
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · -- Check (13, 30)
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · -- Check (16, 105)
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · -- Check (17, 230)
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }