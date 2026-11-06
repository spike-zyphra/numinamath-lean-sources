import Mathlib

theorem algebra_94865 : IsLeast {x : ℕ | ((90 + 80 + 70 + 60 + 85 + x) / 6) ≥ ((90 + 80 + 70 + 60 + 85) / 5 + 3)} 95 := by 
  constructor
  · -- Show 95 is in the set
    norm_num
  · -- Show that if x is in the set, then x ≥ 95
    intro x hx
    have h1 : ((90 + 80 + 70 + 60 + 85 + x) / 6) ≥ ((90 + 80 + 70 + 60 + 85) / 5 + 3) := by 
      simpa using hx
    omega