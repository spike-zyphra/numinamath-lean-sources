import Mathlib

theorem number_theory_3563 (x y : ℤ) : x^2+y^2=(x*y-7)^2 ↔
    (x=7 ∧ y=0) ∨ (x=0 ∧ y=7) ∨ (x=-7 ∧ y=0) ∨ (x=0 ∧ y=-7) ∨
    (x=3 ∧ y=4) ∨ (x=4 ∧ y=3) ∨ (x=-3 ∧ y=-4) ∨ (x=-4 ∧ y=-3) := by
  constructor
  · -- Assume x^2+y^2=(x*y-7)^2, prove the disjunction of the solutions
    intro h
    have h1 : x^2 + y^2 = (x*y-7)^2 := by linarith 
    have eq1 : (x + y - (x * y - 6)) * (x + y + (x * y - 6)) = 13 := by 
      nlinarith [h1]
    have h2 : (x + y - (x * y - 6)) * (x + y + (x * y - 6)) = 13 := eq1 
    have h3 : (x + y - (x * y - 6)) = 1 ∨ (x + y - (x * y - 6)) = 13 ∨ 
        (x + y - (x * y - 6)) = -1 ∨ (x + y - (x * y - 6)) = -13 := by 
      have h4 : (x + y - (x * y - 6)) * (x + y + (x * y - 6)) = 13 := h2
      have h5 : (x + y - (x * y - 6)) ∣ 13 := by
        use (x + y + (x * y - 6))
        all_goals linarith
      have h6 : (x + y - (x * y - 6)) ∣ 13 := h5
      have h7 : (x + y - (x * y - 6)) = 1 ∨ (x + y - (x * y - 6)) = 13 ∨ 
          (x + y - (x * y - 6)) = -1 ∨ (x + y - (x * y - 6)) = -13 := by 
        have h8 : (x + y - (x * y - 6)) ∣ 13 := h6 
        have h9 : (x + y - (x * y - 6)) ≤ 13 := by 
          apply Int.le_of_dvd (show 0 < (13 : ℤ) by norm_num) h8 
        have h10 : (x + y - (x * y - 6)) ≥ -13 := by
          have h11 : (- (x + y - (x * y - 6)) ) ∣ 13 := by 
            exact Int.neg_dvd.2 h8 
          have h12 : - (x + y - (x * y - 6)) ≤ 13 := by 
            apply Int.le_of_dvd (show 0 < (13 : ℤ) by norm_num) h11 
          omega 
        interval_cases (x + y - (x * y - 6)) <;> try { tauto } 
      tauto 
    rcases h3 with (h4 | h4 | h4 | h4)
    · -- Case 1: A = 1, so B = 13.
      have h5 : x + y + (x * y - 6) = 13 := by 
        nlinarith [h4, h2] 
      have h7 : x * y = 12 := by 
        nlinarith 
      have h8 : x + y = 7 := by 
        nlinarith 
      have h9 : (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3) := by 
        have h10 : x ≤ 7 := by nlinarith 
        have h11 : x ≥ 0 := by nlinarith 
        interval_cases x <;> omega 
      rcases h9 with (h10 | h10)
      · -- (3, 4)
        have h11 : x = 3 := h10.1 
        have h12 : y = 4 := h10.2 
        simp [h11, h12] 
      · -- (4, 3)
        have h11 : x = 4 := h10.1 
        have h12 : y = 3 := h10.2 
        simp [h11, h12] 
    · -- Case 2: A = 13, so B = 1.
      have h5 : x + y + (x * y - 6) = 1 := by 
        nlinarith [h4, h2] 
      have h7 : x * y = 0 := by 
        nlinarith 
      have h8 : x + y = 7 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h7) with h9 h9 
      · -- Case x = 0
        have hx : x = 0 := by 
          linarith 
        have hy : y = 7 := by 
          nlinarith 
        simp [hx, hy] 
      · -- Case y = 0
        have hy : y = 0 := by 
          linarith 
        have hx : x = 7 := by 
          nlinarith 
        simp [hx, hy] 
    · -- Case 3: A = -1, so B = -13.
      have h5 : x + y + (x * y - 6) = -13 := by 
        nlinarith [h4, h2] 
      have h7 : x * y = 0 := by 
        nlinarith 
      have h8 : x + y = -7 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h7) with h9 h9 
      · -- Case x = 0
        have hx : x = 0 := by 
          linarith 
        have hy : y = -7 := by 
          nlinarith 
        simp [hx, hy] 
      · -- Case y = 0
        have hy : y = 0 := by 
          linarith 
        have hx : x = -7 := by 
          nlinarith 
        simp [hx, hy] 
    · -- Case 4: A = -13, so B = -1.
      have h5 : x + y + (x * y - 6) = -1 := by 
        nlinarith [h4, h2] 
      have h7 : x * y = 12 := by 
        nlinarith 
      have h8 : x + y = -7 := by 
        nlinarith 
      have h9 : (x = -3 ∧ y = -4) ∨ (x = -4 ∧ y = -3) := by 
        have h10 : x ≤ -3 := by nlinarith 
        have h11 : x ≥ -7 := by nlinarith 
        interval_cases x <;> omega 
      rcases h9 with (h10 | h10)
      · -- (-3, -4)
        have h11 : x = -3 := h10.1 
        have h12 : y = -4 := h10.2 
        simp [h11, h12] 
      · -- (-4, -3)
        have h11 : x = -4 := h10.1 
        have h12 : y = -3 := h10.2 
        simp [h11, h12] 
  · -- Assume the solutions, prove the equation 
    rintro (h | h | h | h | h | h | h | h)
    · -- (7, 0)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (0, 7)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (-7, 0)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (0, -7)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (3, 4)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (4, 3)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (-3, -4)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (-4, -3)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num