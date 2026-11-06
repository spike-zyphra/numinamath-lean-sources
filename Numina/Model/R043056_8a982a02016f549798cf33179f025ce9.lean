import Mathlib

theorem algebra_204547 (a b c d : ℤ) (h : ∀ m n : ℤ, ∃ x y : ℤ, a*x+b*y=m ∧ c*x+d*y=n) :
    |a*d - b*c| = 1 := by
  have eq1 : ∃ x1 y1 : ℤ, a * x1 + b * y1 = 1 ∧ c * x1 + d * y1 = 0 := by
    have h1 := h 1 0
    rcases h1 with ⟨x1, y1, h1a, h1b⟩
    refine ⟨x1, y1, h1a, h1b⟩
  have eq2 : ∃ x2 y2 : ℤ, a * x2 + b * y2 = 0 ∧ c * x2 + d * y2 = 1 := by
    have h2 := h 0 1
    rcases h2 with ⟨x2, y2, h2a, h2b⟩
    refine ⟨x2, y2, h2a, h2b⟩
  rcases eq1 with ⟨x1, y1, h1, h2⟩
  rcases eq2 with ⟨x2, y2, h3, h4⟩
  -- Now we have four equations.
  -- 1. a*x1 + b*y1 = 1
  -- 2. c*x1 + d*y1 = 0
  -- 3. a*x2 + b*y2 = 0
  -- 4. c*x2 + d*y2 = 1
  have eq3 : a * d - b * c = 1 ∨ a * d - b * c = -1 := by
    have eq4 : (a * d - b * c) * (x1 * y2 - x2 * y1) = 1 := by
      nlinarith
    have h3 : (a * d - b * c) * (x1 * y2 - x2 * y1) = 1 := eq4
    have h4 : (a * d - b * c) = 1 ∨ (a * d - b * c) = -1 := by
      have eq8 : (a * d - b * c) * (x1 * y2 - x2 * y1) = 1 := eq4
      have h3 : (a * d - b * c) ∣ 1 := by
        use (x1 * y2 - x2 * y1)
        all_goals linarith
      have h5 : (a * d - b * c) = 1 ∨ (a * d - b * c) = -1 := by
        have h6 : (a * d - b * c) ≤ 1 := by
          exact Int.le_of_dvd (show (0 : ℤ) < 1 by norm_num) h3
        have h7 : (a * d - b * c) ≥ -1 := by
          have h8 : -(a * d - b * c) ∣ 1 := by
            exact Int.neg_dvd.2 h3
          have h9 : -(a * d - b * c) ≤ 1 := by
            exact Int.le_of_dvd (show (0 : ℤ) < 1 by norm_num) h8
          omega
        interval_cases (a * d - b * c) <;> omega
      exact h5
    exact h4
  cases eq3 with
  | inl h5 =>
    rw [h5]
    all_goals norm_num
  | inr h6 =>
    rw [h6]
    all_goals norm_num