import Mathlib


theorem algebra_248837 (a : ℤ) :
    (∃ x y : ℤ, a * (x + y - 1) = x - 2 * y - 1 ∧ a * (x - y - 3) = x + 2 * y - 3) ↔
    a = -5 ∨ a = -3 ∨ a = -1 ∨ a = 1 := by
  constructor
  · -- Assume there exist integer solutions x,y, prove a is in the set.
    rintro ⟨x, y, h1, h2⟩
    have eq1 : x * (a - 1) + y * (a + 2) = a - 1 := by
      linarith
    have eq2 : x * (a - 1) - y * (a + 2) = 3 * a - 3 := by
      linarith
    have eq3 : 2 * y * (a + 2) = -2 * (a - 1) := by
      nlinarith
    have eq4 : y * (a + 2) = 1 - a := by
      linarith
    have h3 : (a + 2) ∣ 3 := by
      use y + 1
      linarith [eq4]
    have h4 : (a + 2) = 1 ∨ (a + 2) = 3 ∨ (a + 2) = -1 ∨ (a + 2) = -3 := by
      have h5 : (a + 2) ∣ 3 := h3
      have h6 : (a + 2) ≤ 3 := by
        apply Int.le_of_dvd (by norm_num) h5
      have h7 : (a + 2) ≥ -3 := by
        have h8 : -( (a + 2) ) ∣ 3 := by
          exact Int.neg_dvd.2 h5
        have h9 : -( (a + 2) ) ≤ 3 := by
          apply Int.le_of_dvd (by norm_num) h8
        linarith
      interval_cases h : (a + 2) <;> tauto
    have h5 : a = -5 ∨ a = -3 ∨ a = -1 ∨ a = 1 := by
      rcases h4 with (h4 | h4 | h4 | h4)
      · -- a + 2 = 1 → a = -1
        have ha1 : a = -1 := by
          omega
        simp [ha1]
      · -- a + 2 = 3 → a = 1
        have ha2 : a = 1 := by
          omega
        simp [ha2]
      · -- a + 2 = -1 → a = -3
        have ha3 : a = -3 := by
          omega
        simp [ha3]
      · -- a + 2 = -3 → a = -5
        have ha4 : a = -5 := by
          omega
        simp [ha4]
    tauto
  · -- Assume a is in the set, prove there exist integer solutions.
    rintro (ha | ha | ha | ha)
    · -- a = -5
      rw [ha]
      use 2, -2
      all_goals
        norm_num
    · -- a = -3
      rw [ha]
      use 2, -4
      all_goals
        norm_num
    · -- a = -1
      rw [ha]
      use 2, 2
      all_goals
        norm_num
    · -- a = 1
      rw [ha]
      use 0, 0
      all_goals
        norm_num