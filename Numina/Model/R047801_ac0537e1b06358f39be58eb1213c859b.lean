import Mathlib

theorem algebra_20840 (x y z : ℝ) :
    x + y - z = 0 ∧ x * z - x * y + y * z = 27 ∧ x * y * z = 54 ↔
    (x = 3 ∧ y = 3 ∧ z = 6) ∨ (x = 3 ∧ y = -6 ∧ z = -3) ∨ (x = -6 ∧ y = 3 ∧ z = -3) := by
  constructor
  · -- Assume the system of equations, prove the solutions
    rintro ⟨h1, h2, h3⟩
    have h4 : z = x + y := by 
      linarith
    have h5 : x ^ 2 + x * y + y ^ 2 = 27 := by
      rw [h4] at h2
      nlinarith
    have h6 : x * y * (x + y) = 54 := by
      rw [h4] at h3
      linarith
    have h7 : (x + y) ^ 3 - 27 * (x + y) - 54 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 6), sq_nonneg (x + y + 3)]
    -- ((x + y) - 6) * ((x + y) + 3) ^ 2 = 0
    have h8 : ((x + y) - 6) * ((x + y) + 3) ^ 2 = 0 := by 
      nlinarith
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- Case: x + y = 6
      have h11 : x + y = 6 := by linarith 
      have h12 : x * y = 9 := by
        nlinarith 
      have h13 : (x - 3) * (y - 3) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 h13) with h14 h15
      · -- Case: x = 3 
        have hx : x = 3 := by linarith 
        -- Then y = 3
        have hy : y = 3 := by 
          nlinarith 
        have h16 : z = 6 := by 
          linarith 
        left 
        exact ⟨hx, hy, h16⟩
      · -- Case: y = 3 
        have hy : y = 3 := by linarith 
        -- Then x = 3
        have hx : x = 3 := by 
          nlinarith 
        have h16 : z = 6 := by 
          linarith 
        left 
        exact ⟨hx, hy, h16⟩
    · -- Case: (x + y + 3) ^ 2 = 0 
      have h17 : x + y = -3 := by 
        nlinarith 
      have h18 : x * y = -18 := by 
        nlinarith 
      have h19 : (x - 3) * (x + 6) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 h19) with h20 h21 
      · -- Case: x = 3 
        have h22 : x = 3 := by linarith 
        have h23 : y = -6 := by 
          nlinarith 
        have h24 : z = -3 := by 
          nlinarith 
        right 
        left 
        exact ⟨h22, h23, h24⟩
      · -- Case: x = -6 
        have h25 : x = -6 := by linarith 
        have h26 : y = 3 := by 
          nlinarith 
        have h27 : z = -3 := by 
          nlinarith 
        right 
        right 
        exact ⟨h25, h26, h27⟩
  · -- Assume the solutions, prove the system
    rintro (h | h | h)
    -- First solution
    · -- First solution 
      rcases h with ⟨hx, hy, hz⟩
      constructor 
      · -- First equation 
        linarith 
      constructor 
      · -- Second equation 
        rw [hx, hy, hz]
        norm_num 
      · -- Third equation 
        rw [hx, hy, hz]
        norm_num 
    · -- Second solution 
      rcases h with ⟨hx, hy, hz⟩
      constructor 
      · -- First equation 
        linarith 
      constructor 
      · -- Second equation 
        rw [hx, hy, hz]
        norm_num 
      · -- Third equation 
        rw [hx, hy, hz]
        norm_num 
    · -- Third solution 
      rcases h with ⟨hx, hy, hz⟩ 
      constructor 
      · -- First equation 
        linarith 
      constructor 
      · -- Second equation 
        rw [hx, hy, hz]
        norm_num 
      · -- Third equation 
        rw [hx, hy, hz]
        norm_num