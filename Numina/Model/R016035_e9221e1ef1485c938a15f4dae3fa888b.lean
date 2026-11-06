import Mathlib

theorem algebra_316364 :
    {(x, y) : ℤ × ℤ | x^2 = y^2 + 4 * y + 20}.ncard = 6 := by
  have h1 : {(x, y) : ℤ × ℤ | x^2 = y^2 + 4 * y + 20} = {(-5, 1), (-4, -2), (-5, -5), (4, -2), (5, -5), (5, 1)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Forward direction: if (x, y) satisfies the equation, then it's one of these 6.
      rintro H
      have h2 : (x + (y + 2)) * (x - (y + 2)) = 16 := by
        nlinarith
      have h4 : (x + (y + 2)) ∣ 16 := by
        use (x - (y + 2))
        all_goals linarith
      have h5 : (x + (y + 2)) = 1 ∨ (x + (y + 2)) = 2 ∨ (x + (y + 2)) = 4 ∨ (x + (y + 2)) = 8 ∨ (x + (y + 2)) = 16 ∨ (x + (y + 2)) = -1 ∨ (x + (y + 2)) = -2 ∨ (x + (y + 2)) = -4 ∨ (x + (y + 2)) = -8 ∨ (x + (y + 2)) = -16 := by
        have h11 : (x + (y + 2)) ∣ 16 := h4
        have h12 : (x + (y + 2)) ≤ 16 := by
          exact Int.le_of_dvd (by norm_num) h11
        have h13 : (x + (y + 2)) ≥ -16 := by
          have h14 : (- (x + (y + 2)) ) ∣ 16 := by
            exact Int.neg_dvd.2 h11
          have h15 : - (x + (y + 2)) ≤ 16 := by
            exact Int.le_of_dvd (by norm_num) h14
          linarith
        interval_cases h5 : (x + (y + 2)) <;> try { tauto }
      rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5)
      · -- Case where x + (y + 2) = 1
        have h6 : (x - (y + 2)) = 16 := by
          nlinarith
        omega
      · -- Case where x + (y + 2) = 2
        have h6 : (x - (y + 2)) = 8 := by
          nlinarith
        have hx : x = 5 := by
          omega
        have hy : y = -5 := by
          omega
        simp [hx, hy]
      · -- Case where x + (y + 2) = 4
        have h6 : (x - (y + 2)) = 4 := by
          nlinarith
        have hx : x = 4 := by
          omega
        have hy : y = -2 := by
          omega
        simp [hx, hy]
      · --  Case where x + (y + 2) = 8
        have h6 : (x - (y + 2)) = 2 := by
          nlinarith
        have hx : x = 5 := by
          omega
        have hy : y = 1 := by
          omega
        simp [hx, hy]
      · --  Case where x + (y + 2) = 16
        have h6 : (x - (y + 2)) = 1 := by
          nlinarith
        omega
      · -- Case where x + (y + 2) = -1
        have h6 : (x - (y + 2)) = -16 := by
          nlinarith
        omega
      · --  Case where x + (y + 2) = -2
        have h6 : (x - (y + 2)) = -8 := by
          nlinarith
        have hx : x = -5 := by
          omega
        have hy : y = 1 := by
          omega
        simp [hx, hy]
      · --  Case where x + (y + 2) = -4
        have h6 : (x - (y + 2)) = -4 := by
          nlinarith
        have hx : x = -4 := by
          omega
        have hy : y = -2 := by
          omega
        simp [hx, hy]
      · --  Case where x + (y + 2) = -8
        have h6 : (x - (y + 2)) = -2 := by
          nlinarith
        have hx : x = -5 := by
          omega
        have hy : y = -5 := by
          omega
        simp [hx, hy]
      · --  Case where x + (y + 2) = -16
        have h6 : (x - (y + 2)) = -1 := by
          nlinarith
        omega
    · -- Backward direction: if (x, y) in the set, then it satisfies the equation.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }