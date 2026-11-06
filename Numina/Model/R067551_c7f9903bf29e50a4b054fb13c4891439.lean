import Mathlib

theorem number_theory_172271 (x y : ℤ) :
    ∃ p a : ℕ, Nat.Prime p ∧ x^2 + y^2 = p ∧ (x + y)^2 - a^2 = p ↔
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨ (x = -1 ∧ y = -2) ∨ (x = -2 ∧ y = -1) := by 
  use 5
  use 2
  constructor
  · -- Forward direction: if the equations hold, then (x,y) is among the four possible pairs
    intro h
    rcases h with ⟨h_prime, h_eq_p, h_eq_p2⟩
    have h1 : x^2 + y^2 = (5 : ℤ) := by
      norm_num at h_eq_p ⊢
      linarith
    have h2 : (x + y : ℤ)^2 - (2 : ℤ) ^ 2 = (5 : ℤ) := by
      norm_num at h_eq_p2 ⊢
      linarith
    have h3 : (x + y : ℤ) ^ 2 = 9 := by 
      have h4 : (x + y : ℤ) ^ 2 - 4 = 5 := by
        nlinarith 
      nlinarith [h4]
    have h4 : x + y = 3 ∨ x + y = -3 := by 
      have h : (x + y : ℤ) ^ 2 = 9 := h3
      have : (x + y : ℤ) = 3 ∨ (x + y : ℤ) = -3 := by 
        have h1 : (x + y : ℤ) ^ 2 - 9 = 0 := by linarith 
        have h2 : ((x + y : ℤ) - 3) * ((x + y : ℤ) + 3) = 0 := by 
          linarith 
        cases' (mul_eq_zero.mp h2) with h3 h4 
        · -- Case: (x + y) - 3 = 0 
          left 
          linarith 
        · -- Case: (x + y) + 3 = 0 
          right 
          linarith 
      assumption 
    cases' h4 with h4 h4
    · -- Case where x + y = 3 
      have h5 : y = 3 - x := by 
        linarith 
      rw [h5] at h1 
      have h6 : (x : ℤ)^2 + (3 - x : ℤ)^2 = 5 := by 
        nlinarith 
      have h7 : (x - 1) * (x - 2) = 0 := by 
        nlinarith [h6]
      cases' (mul_eq_zero.mp h7) with h8 h9 
      · -- Case: x - 1 = 0 
        have hx : x = 1 := by linarith 
        have hy : y = 2 := by 
          linarith [hx, h5] 
        left 
        exact ⟨hx, hy⟩ 
      · -- Case: x - 2 = 0 
        have hx : x = 2 := by linarith 
        have hy : y = 1 := by 
          linarith [hx, h5] 
        right 
        left 
        exact ⟨hx, hy⟩ 
    · -- Case where x + y = -3 
      have h5 : y = -3 - x := by 
        linarith 
      rw [h5] at h1 
      have h6 : (x : ℤ)^2 + (-3 - x : ℤ)^2 = 5 := by 
        nlinarith 
      have h7 : (x + 1) * (x + 2) = 0 := by 
        nlinarith [h6]
      cases' (mul_eq_zero.mp h7) with h8 h9 
      · -- Case: x + 1 = 0 
        have hx : x = -1 := by linarith 
        have hy : y = -2 := by 
          linarith [hx, h5] 
        right 
        right 
        left 
        exact ⟨hx, hy⟩ 
      · -- Case: x + 2 = 0 
        have hx : x = -2 := by linarith 
        have hy : y = -1 := by 
          linarith [hx, h5] 
        right 
        right 
        right 
        exact ⟨hx, hy⟩ 
  · -- Backward direction: given one of the four pairs, the equations hold 
    rintro (h | h | h | h)
    · -- Case where (x = 1 ∧ y = 2)
      rcases h with ⟨hx, hy⟩
      constructor
      · norm_num 
      constructor
      · norm_num [hx, hy]
      · norm_num [hx, hy]
    · -- Case where (x = 2 ∧ y = 1)
      rcases h with ⟨hx, hy⟩
      constructor
      · norm_num 
      constructor
      · norm_num [hx, hy]
      · norm_num [hx, hy]
    · -- Case where (x = -1 ∧ y = -2)
      rcases h with ⟨hx, hy⟩
      constructor
      · norm_num 
      constructor
      · norm_num [hx, hy]
      · norm_num [hx, hy]
    · -- Case where (x = -2 ∧ y = -1)
      rcases h with ⟨hx, hy⟩
      constructor
      · norm_num 
      constructor
      · norm_num [hx, hy]
      · norm_num [hx, hy]