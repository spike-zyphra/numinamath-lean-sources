import Mathlib

theorem number_theory_114713 (x y : ℕ) :
    65 * x - 43 * y = 2 ↔ ∃ n : ℤ, x = 4 - 43 * n ∧ y = 6 - 65 * n := by 
  constructor 
  · -- Forward implication: if 65x - 43y = 2 then (x =4 -43n ∧ y=6 -65n).
    intro h 
    have eq1 : (65 : ℤ) * (x : ℤ) - (43 : ℤ) * (y : ℤ) = (2 : ℤ) := by 
      omega 
    -- Now need to show exists a integer n such that 
    have h2 : ∃ n : ℤ, x = 4 - 43 * n ∧ y = 6 - 65 * n := by
      use (4 - (x : ℤ)) / 43 
      constructor
      · -- Show x = 4 - 43 * ( (4 - (x : ℤ)) / 43 )
        have h3 : (65 : ℤ) * (x : ℤ) - (43 : ℤ) * (y : ℤ) = (2 : ℤ) := by 
          omega 
        have h4 : (x : ℤ) % 43 = 4 := by
          omega 
        have h5 : (x : ℤ) = 4 - 43 * ((4 - (x : ℤ)) / 43) := by 
          omega 
        omega 
      · -- Show y = 6 - 65 * ( (4 - (x : ℤ)) / 43 )
        have h3 : (65 : ℤ) * (x : ℤ) - (43 : ℤ) * (y : ℤ) = (2 : ℤ) := by 
          omega 
        have h4 : (x : ℤ) % 43 = 4 := by
          omega 
        have h6 : (y : ℤ) = 6 - 65 * ((4 - (x : ℤ)) / 43) := by 
          omega 
        omega 
    exact h2
  · -- Backward implication: if exists n, then 65 x -43 y = 2.
    rintro ⟨n, hx, hy⟩ 
    have eq_x : (x : ℤ) = 4 - 43 * (n : ℤ) := by
      omega 
    have eq_y : (y : ℤ) = 6 - 65 * (n : ℤ) := by 
      omega 
    have eq1 : (65 : ℤ) * (x : ℤ) - (43 : ℤ) * (y : ℤ) = (2 : ℤ) := by 
      rw [eq_x, eq_y] 
      all_goals omega 
    omega