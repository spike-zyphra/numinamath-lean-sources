import Mathlib

theorem algebra_245617 (x y : ℤ) :
    x^2 * (y - 1) + y^2 * (x - 1) = 1 ↔
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨ (x = -5 ∧ y = 2) ∨ (x = 2 ∧ y = -5) := by
  constructor
  · -- Forward implication
    rintro h
    have h1 : (x + y) ^ 2 - (x * y) * (x + y) - 2 * (x * y) + 1 = 0 := by
      nlinarith 
    have h3 : (x + y + 2) ∣ 5 := by
      have h3 : (x + y + 2) ∣ ((x + y) ^ 2 + 1) := by
        use x * y
        nlinarith
      have h4 : (x + y + 2) ∣ 5 := by
        have h5 : (x + y + 2) ∣ ((x + y) ^ 2 + 1 - (x + y + 2) * (x + y - 2)) := by 
          apply Dvd.dvd.sub 
          exact h3 
          exact dvd_mul_right (x + y + 2) (x + y - 2)
        have eq1 : (x + y) ^ 2 + 1 - (x + y + 2) * (x + y - 2) = 5 := by
          ring 
        rw [eq1] at h5 
        exact h5 
      exact h4 
    have h4 : (x + y + 2) = 1 ∨ (x + y + 2) = -1 ∨ (x + y + 2) = 5 ∨ (x + y + 2) = -5 := by 
      have h6 : (x + y + 2) ∣ 5 := h3 
      have h7 : (x + y + 2) ≤ 5 := by 
        apply Int.le_of_dvd (show (0 : ℤ) < 5 by norm_num) h6 
      have h8 : (x + y + 2) ≥ -5 := by 
        have h9 : -(x + y + 2) ∣ 5 := by 
          exact Int.neg_dvd.2 h6 
        have h10 : -(x + y + 2) ≤ 5 := by 
          apply Int.le_of_dvd (show (0 : ℤ) < 5 by norm_num) h9 
        linarith 
      interval_cases h : (x + y + 2) <;> tauto
    rcases h4 with (h5 | h5 | h5 | h5)
    · 
      have h10 : x + y + 2 = 1 := by linarith
      have h11 : x + y = -1 := by linarith 
      have h12 : x * y = 2 := by 
        rw [show x + y = -1 by linarith] at h1
        nlinarith 
      -- Solving x * y = 2 and x + y = -1
      have h13 : x ≤ 2 := by
        have h200 : x * (y) = 2 := by linarith 
        have h14 : x ∣ 2 := by 
          use y 
          all_goals 
            nlinarith 
        have h15 : x ≤ 2 := by 
          apply Int.le_of_dvd (show (0 : ℤ) < 2 by norm_num) h14 
        linarith 
      have h14 : x ≥ -2 := by 
        have h200 : x * (y) = 2 := by linarith
        have h1010 : x ∣ 2 := by 
          use y 
          all_goals 
            nlinarith 
        have h1020 : -x ∣ 2 := by
          exact Int.neg_dvd.2 h1010
        have h1030 : -x ≤ 2 := by
          apply Int.le_of_dvd (show (0 : ℤ) < 2 by norm_num) h1020 
        linarith
      interval_cases x <;> omega 
    · 
      have h10 : x + y + 2 = -1 := by linarith 
      have h11 : x + y = -3 := by linarith 
      have h12 : x * y = -10 := by 
        rw [show x + y = -3 by linarith] at h1
        nlinarith 
      have h41 : (x = 2 ∧ y = -5) ∨ (x = -5 ∧ y = 2) := by 
        have h40 : x * (y) = -10 := by linarith 
        have h41 : x + y = -3 := by linarith 
        have h21 : y = -3 - x := by 
          linarith 
        rw [show y = -3 - x by linarith] at h40 
        have h400 : x * (-3 - x) = -10 := by 
          nlinarith 
        have eq1 : (x - 2) * (x + 5) = 0 := by
          nlinarith 
        cases' (mul_eq_zero.1 eq1) with h14 h15
        · 
          have hx11 : x = 2 := by linarith 
          have hy11 : y = -5 := by 
            nlinarith 
          left 
          tauto 
        · 
          have hx11 : x = -5 := by linarith 
          have hy11 : y = 2 := by 
            nlinarith 
          right 
          tauto 
      tauto 
    · 
      have h10 : x + y + 2 = 5 := by linarith 
      have h11 : x + y = 3 := by linarith 
      have h12 : x * y = 2 := by 
        rw [show x + y = 3 by linarith] at h1
        nlinarith 
      have h14 : (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) := by 
        have h140 : x * (y) = 2 := by linarith 
        have h141 : x + y = 3 := by linarith 
        have h21 : y = 3 - x := by 
          linarith 
        rw [show y = 3 - x by linarith] at h140 
        have h1400 : x * (3 - x) = 2 := by 
          nlinarith 
        have eq1 : (x - 1) * (x - 2) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 eq1) with h14 h15
        · 
          have hx22 : x = 1 := by linarith 
          have hy22 : y = 2 := by 
            nlinarith 
          left 
          tauto 
        · 
          have hx22 : x = 2 := by linarith 
          have hy22 : y = 1 := by 
            nlinarith 
          right 
          tauto 
      tauto 
    · 
      have h10 : x + y + 2 = -5 := by linarith 
      have h11 : x + y = -7 := by linarith 
      have h12 : x * y = -10 := by 
        rw [show x + y = -7 by linarith] at h1
        nlinarith 
      -- Solving x * y = -10 and x + y = -7
      have h13 : x ≤ 10 := by
        have h200 : x * (y) = -10 := by linarith 
        have h14 : x ∣ -10 := by 
          use y 
          all_goals 
            nlinarith 
        have h1500 : x ∣ 10 := by 
          exact Int.dvd_neg.mp h14 
        have h2000 : x ≤ 10 := by
          apply Int.le_of_dvd (show 0 < 10 by norm_num) h1500 
        linarith 
      have h14 : x ≥ -10 := by 
        have h200 : x * (y) = -10 := by linarith 
        have h1500 : x ∣ 10 := by
          have h14 : x ∣ -10 := by 
            use y 
            all_goals 
              nlinarith 
          exact Int.dvd_neg.mp h14 
        have h1010 : -x ∣ 10 := by 
          exact Int.neg_dvd.2 h1500 
        have h1020 : -x ≤ 10 := by 
          apply Int.le_of_dvd (show (0 : ℤ) < 10 by norm_num) h1010 
        linarith 
      interval_cases x <;> omega 
  · -- Backward implication
    rintro (h | h | h | h)
    · 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num