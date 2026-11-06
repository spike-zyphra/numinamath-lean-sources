import Mathlib

theorem algebra_106456 (x y : ℤ) :
    2 * x ^ 3 + x * y - 7 = 0 ↔
    (x = -7 ∧ y = -99) ∨ (x = -1 ∧ y = -9) ∨ (x = 1 ∧ y = 5) ∨ (x = 7 ∧ y = -97) := by 
  constructor
  · -- Assume 2x^3 + x*y -7 =0, prove (x,y) is one of the four solutions
    intro h
    have h1 : x ∣ 7 := by 
      use 2 * x^2 + y 
      linarith 
    have h2 : x = 1 ∨ x = -1 ∨ x = 7 ∨ x = -7 := by
      have h3 : x ≤ 7 := by 
        apply Int.le_of_dvd (by norm_num) h1
      have h4 : x ≥ -7 := by
        have h5 : -x ∣ 7 := by 
          exact Int.neg_dvd.2 h1
        have h6 : -x ≤ 7 := by 
          apply Int.le_of_dvd (by norm_num) h5
        linarith
      interval_cases x <;> tauto
    rcases h2 with (rfl | rfl | rfl | rfl)
    · -- Case x =1
      have hy1 : y = 5 := by 
        linarith
      exact Or.inr (Or.inr (Or.inl ⟨by trivial, by linarith⟩))
    · -- Case x = -1
      have hy2 : y = -9 := by 
        linarith
      exact Or.inr (Or.inl ⟨by trivial, by linarith⟩)
    · -- Case x =7
      have hy3 : y = -97 := by 
        linarith
      exact Or.inr (Or.inr (Or.inr ⟨by trivial, by linarith⟩))
    · -- Case x = -7
      have hy4 : y = -99 := by 
        linarith
      exact Or.inl ⟨by trivial, by linarith⟩
  · -- Show that the solutions satisfy the equation
    rintro (h | h | h | h)
    · -- Case x = -7, y = -99 
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case x = -1, y = -9 
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case x =1, y =5 
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case x =7, y =-97 
      rcases h with ⟨rfl, rfl⟩
      norm_num