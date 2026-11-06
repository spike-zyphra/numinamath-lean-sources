import Mathlib

theorem algebra_248630 (x y z : ℝ) :
    x + y = z ∧ x^2 + y^2 = z ∧ x^3 + y^3 = z ↔
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 1 ∧ z = 1) ∨
    (x = 1 ∧ y = 0 ∧ z = 1) ∨ (x = 1 ∧ y = 1 ∧ z = 2) := by
  constructor 
  · -- Assume the three equations hold, prove one of the four solutions 
    rintro ⟨h1, h2, h3⟩ 
    have h4 : z = x + y := by linarith 
    rw [h4] at h2 h3 
    have h5 : x^2 + y^2 = x + y := by 
      nlinarith 
    have h6 : x^3 + y^3 = x + y := by
      nlinarith 
    have h7 : (x + y) * (x + y - x * y - 1) = 0 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
    cases' (mul_eq_zero.1 h7) with h8 h9 
    · -- Case where x + y = 0 
      have hy : y = -x := by linarith 
      rw [hy] at h5 
      have h10 : x = 0 := by 
        nlinarith 
      have hy0 : y = 0 := by linarith 
      have h30 : z = 0 := by linarith 
      left 
      exact ⟨h10, hy0, h30⟩ 
    · -- Case where x + y - x * y - 1 = 0 
      have h6 : (x - 1) * (y - 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 h6) with h7 h8 
      · -- Case where x - 1 = 0, so x = 1 
        have hx1 : x = 1 := by linarith 
        have h10 : y^2 - y = 0 := by 
          rw [hx1] at h5 
          nlinarith 
        have h11 : y * (y - 1) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h11) with h12 h13 
        · -- Case where y = 0 
          have hy0 : y = 0 := by linarith 
          have h31 : z = 1 := by 
            nlinarith [hx1, hy0] 
          right 
          right 
          left 
          exact ⟨hx1, hy0, h31⟩ 
        · -- Case where y - 1 = 0 
          have hy1 : y = 1 := by linarith 
          have h32 : z = 2 := by 
            nlinarith [hx1, hy1] 
          right 
          right 
          right 
          exact ⟨hx1, hy1, h32⟩ 
      · -- Case where y - 1 = 0, so y = 1 
        have hy1 : y = 1 := by linarith 
        have h12 : x^2 - x = 0 := by 
          rw [hy1] at h5 
          nlinarith 
        have h13 : x * (x - 1) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h13) with h14 h15 
        · -- Case where x = 0 
          have hx0 : x = 0 := by linarith 
          have h31 : z = 1 := by 
            nlinarith [hx0, hy1] 
          right 
          left 
          exact ⟨hx0, hy1, h31⟩ 
        · -- Case where x - 1 = 0 
          have hx1 : x = 1 := by linarith 
          have h32 : z = 2 := by 
            nlinarith [hx1, hy1] 
          right 
          right 
          right 
          exact ⟨hx1, hy1, h32⟩ 
  · -- Prove the converse: each solution satisfies the system 
    rintro (h | h | h | h) 
    · -- (0, 0, 0) 
      rcases h with ⟨rfl, rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num 
    · -- (0, 1, 1) 
      rcases h with ⟨rfl, rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num 
    · -- (1, 0, 1) 
      rcases h with ⟨rfl, rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num 
    · -- (1, 1, 2) 
      rcases h with ⟨rfl, rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num