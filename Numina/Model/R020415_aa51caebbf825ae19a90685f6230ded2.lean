import Mathlib

theorem algebra_12926 (a : ℕ+ → ℤ) (h : ∀ n, a (n + 2) = 6 * a n - a (n + 1))
    (ha1 : a 1 = 5) (ha2 : a 2 = 7) :
    a 10 + 3 * a 9 = 5632 := by

  have ha3 : a 3 = 23 := by
    have eq1 : a 3 = 6 * a 1 - a 2 := by
      specialize h 1 
      simpa using h
    rw [eq1] 
    rw [ha1, ha2] 
    all_goals norm_num

  have ha4 : a 4 = 19 := by
    have eq1 : a 4 = 6 * a 2 - a 3 := by
      specialize h 2 
      simpa using h
    rw [eq1] 
    rw [ha2, ha3] 
    all_goals norm_num

  have ha5 : a 5 = 119 := by 
    have eq1 : a 5 = 6 * a 3 - a 4 := by
      specialize h 3 
      simpa using h
    rw [eq1] 
    rw [ha3, ha4] 
    all_goals norm_num

  have ha6 : a 6 = -5 := by 
    have eq1 : a 6 = 6 * a 4 - a 5 := by 
      specialize h 4 
      simpa using h
    rw [eq1] 
    rw [ha4, ha5] 
    all_goals norm_num

  have ha7 : a 7 = 719 := by 
    have eq1 : a 7 = 6 * a 5 - a 6 := by
      specialize h 5 
      simpa using h
    rw [eq1] 
    rw [ha5, ha6] 
    all_goals norm_num

  have ha8 : a 8 = -749 := by 
    have eq1 : a 8 = 6 * a 6 - a 7 := by 
      specialize h 6 
      simpa using h
    rw [eq1] 
    rw [ha6, ha7] 
    all_goals norm_num

  have ha9 : a 9 = 5063 := by
    have eq1 : a 9 = 6 * a 7 - a 8 := by 
      specialize h 7 
      simpa using h 
    rw [eq1] 
    rw [ha7, ha8] 
    all_goals norm_num

  have ha10 : a 10 = -9557 := by 
    have eq1 : a 10 = 6 * a 8 - a 9 := by 
      specialize h 8 
      simpa using h 
    rw [eq1] 
    rw [ha8, ha9] 
    all_goals norm_num

  rw [ha10, ha9] 
  all_goals norm_num