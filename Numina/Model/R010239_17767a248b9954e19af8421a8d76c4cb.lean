import Mathlib

theorem algebra_17070 :
    IsLeast {n : ℕ | 10 * n > 2000 + 5 * n} 401 := by 
  constructor
  · -- Show 401 is in the set
    show 10 * 401 > 2000 + 5 * 401
    norm_num
  · -- Show that for all n in the set, 401 ≤ n
    intro n
    intro hn
    have h : 10 * n > 2000 + 5 * n := by
      simpa using hn
    omega