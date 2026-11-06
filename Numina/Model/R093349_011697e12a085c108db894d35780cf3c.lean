import Mathlib

theorem algebra_12877 : IsGreatest {x : ℤ | (x / 3 : ℚ) + 4 / 5 < 5 / 3} 2 := by
  constructor
  · -- Show that 2 is in the set
    norm_num
  · -- Show that for any integer x in the set, x ≤ 2
    intro x
    intro hx
    have h1 : (x / 3 : ℚ) + 4 / 5 < 5 / 3 := by
      simpa using hx
    have h3 : x * 5 < 13 := by
      have hfrac : (x : ℚ) / 3 + 4 / 5 < 5 / 3 := by 
        linarith
      have h : (x : ℚ) * 5 < 13 := by
        linarith
      exact_mod_cast h
    have h4 : x ≤ 2 := by
      linarith
    linarith