import Mathlib

theorem number_theory_218159 (x y : ℤ) :
    x^2 - y^2 = 203 ↔
    (x = 102 ∧ y = 101) ∨ (x = 102 ∧ y = -101) ∨ (x = -102 ∧ y = 101) ∨
    (x = -102 ∧ y = -101) ∨ (x = 18 ∧ y = 11) ∨ (x = -18 ∧ y = 11) ∨
    (x = 18 ∧ y = -11) ∨ (x = -18 ∧ y = -11) := by 
  constructor
  · -- Assume x^2 - y^2 = 203, prove the disjunction
    intro h
    have h1 : x^2 - y^2 = 203 := h
    have h2 : (x - y) * (x + y) = 203 := by
      linarith [h1]
    have h3 : x - y ∣ 203 := by 
      use x + y
      all_goals linarith
    have h4 : x - y ≤ 203 := by
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : x - y ≥ -203 := by
      have h6 : - (x - y) ∣ 203 := by 
        exact Int.neg_dvd.2 h3
      have h7 : - (x - y) ≤ 203 := by 
        apply Int.le_of_dvd (by norm_num) h6
      omega
    interval_cases h6 : x - y <;> omega 
  · -- Assume the disjunction, prove x^2 - y^2 = 203
    rintro (h | h | h | h | h | h | h | h)
    · -- Case (x = 102 ∧ y = 101)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case (x = 102 ∧ y = -101)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case (x = -102 ∧ y = 101)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · --  (x = -102 ∧ y = -101)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · --  (x = 18 ∧ y = 11)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · --  (x = -18 ∧ y = 11)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · --  (x = 18 ∧ y = -11)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · --  (x = -18 ∧ y = -11)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num