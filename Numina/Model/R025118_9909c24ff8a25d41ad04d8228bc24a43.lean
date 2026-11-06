import Mathlib

theorem algebra_298924 :
    {(x, y, z) : ℤ × ℤ × ℤ | x^2 + x * y + x * z = 10 ∧ y * z + y^2 = 15}.ncard = 4 := by 
  have h1 : {(x, y, z) : ℤ × ℤ × ℤ | x^2 + x * y + x * z = 10 ∧ y * z + y^2 = 15} = {(-5, 5, -2), (2, 5, -2), (-2, -5, 2), (5, -5, 2)} := by
    ext ⟨x, y, z⟩
    simp [-mul_add, -add_mul]
    constructor
    · -- Assume (x, y, z) satisfies both equations, prove (x,y, z) ∈ RHS
      rintro ⟨h1, h2⟩
      have h3 : y * (z + y) = 15 := by
        nlinarith
      have h4 : y ∣ 15 := by 
        use z + y
        all_goals linarith
      have h5 : y = -15 ∨ y = -5 ∨ y = -3 ∨ y = -1 ∨ y = 1 ∨ y = 3 ∨ y = 5 ∨ y = 15 := by
        have h6 : y ∣ 15 := h4
        have h7 : y ≤ 15 := by
          exact Int.le_of_dvd (by norm_num) h6
        have h8 : y ≥ -15 := by
          have h9 : -y ∣ 15 := by
            exact Int.neg_dvd.2 h6
          have h10 : -y ≤ 15 := by
            exact Int.le_of_dvd (by norm_num) h9
          linarith
        interval_cases y <;> tauto
      rcases h5 with (r | r | r | r | r | r | r | r)
      · -- y = -15
        rw [show y = -15 by linarith] at h3 h1
        have h10 : z = 14 := by 
          nlinarith
        rw [show z = 14 by linarith] at h1
        have h11 : x^2 - x - 10 = 0 := by
          nlinarith
        have h12 : x ≤ 4 := by 
          nlinarith [sq_nonneg (x - 3)]
        have h13 : x ≥ -3 := by 
          nlinarith [sq_nonneg (x + 3)]
        interval_cases x <;> omega
      · -- y = -5
        rw [show y = -5 by linarith] at h3 h1
        have h10 : z = 2 := by 
          nlinarith
        rw [show z = 2 by linarith] at h1
        have h11 : x^2 - 3 * x - 10 = 0 := by
          nlinarith
        have h12 : (x - 5) * (x + 2) = 0 := by 
          nlinarith
        cases' (mul_eq_zero.mp h12) with h13 h14
        · -- x = 5
          have hx : x = 5 := by linarith
          simp [hx, show y = -5 by linarith, show z = 2 by linarith]
        · -- x = -2
          have hx : x = -2 := by linarith
          simp [hx, show y = -5 by linarith, show z = 2 by linarith]
      · -- y = -3
        rw [show y = -3 by linarith] at h3 h1
        have h10 : z = -2 := by 
          nlinarith
        rw [show z = -2 by linarith] at h1
        have h11 : x^2 - 5 * x - 10 = 0 := by
          nlinarith
        have h12 : x ≤ 7 := by 
          nlinarith [sq_nonneg (x - 3)]
        have h13 : x ≥ -4 := by 
          nlinarith [sq_nonneg (x + 4)]
        interval_cases x <;> omega
      · -- y = -1
        rw [show y = -1 by linarith] at h3 h1
        have h10 : z = -14 := by 
          nlinarith
        rw [show z = -14 by linarith] at h1
        have h11 : x^2 - 15 * x - 10 = 0 := by
          nlinarith
        have h12 : x ≤ 17 := by 
          nlinarith [sq_nonneg (x - 8)]
        have h13 : x ≥ -2 := by 
          nlinarith [sq_nonneg (x + 2)]
        interval_cases x <;> omega
      · -- y = 1
        rw [show y = 1 by linarith] at h3 h1
        have h10 : z = 14 := by 
          nlinarith
        rw [show z = 14 by linarith] at h1
        have h11 : x^2 + 15 * x - 10 = 0 := by
          nlinarith
        have h12 : x ≤ 1 := by 
          nlinarith [sq_nonneg (x + 8)]
        have h13 : x ≥ -17 := by 
          nlinarith [sq_nonneg (x + 8)]
        interval_cases x <;> omega
      · -- y = 3
        rw [show y = 3 by linarith] at h3 h1
        have h10 : z = 2 := by 
          nlinarith
        rw [show z = 2 by linarith] at h1
        have h11 : x^2 + 5 * x - 10 = 0 := by
          nlinarith
        have h12 : x ≤ 2 := by 
          nlinarith [sq_nonneg (x + 3)]
        have h13 : x ≥ -7 := by 
          nlinarith [sq_nonneg (x + 3)]
        interval_cases x <;> omega
      · -- y = 5
        rw [show y = 5 by linarith] at h3 h1
        have h10 : z = -2 := by 
          nlinarith
        rw [show z = -2 by linarith] at h1
        have h11 : x^2 + 3 * x - 10 = 0 := by
          nlinarith
        have h12 : (x - 2) * (x + 5) = 0 := by 
          nlinarith
        cases' (mul_eq_zero.mp h12) with h13 h14
        · -- x = 2
          have hx : x = 2 := by linarith
          simp [hx, show y = 5 by linarith, show z = -2 by linarith]
        · -- x = -5
          have hx : x = -5 := by linarith
          simp [hx, show y = 5 by linarith, show z = -2 by linarith]
      · -- y = 15
        rw [show y = 15 by linarith] at h3 h1
        have h10 : z = -14 := by 
          nlinarith
        rw [show z = -14 by linarith] at h1
        have h11 : x^2 + x - 10 = 0 := by
          nlinarith
        have h12 : x ≤ 3 := by 
          nlinarith [sq_nonneg (x + 2)]
        have h13 : x ≥ -4 := by 
          nlinarith [sq_nonneg (x + 2)]
        interval_cases x <;> omega
    · -- Assume (x,y, z) ∈ RHS, prove it satisfies both equations
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp