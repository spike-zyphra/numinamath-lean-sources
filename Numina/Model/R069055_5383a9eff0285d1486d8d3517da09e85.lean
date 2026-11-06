import Mathlib

theorem algebra_14257 : IsLeast {d | 9 ∣ (437000 + 100 * d + 3)} 1 := by
  constructor 
  · -- Show that 1 is in the set
    show 9 ∣ (437000 + 100 * 1 + 3)
    norm_num
  · -- Show that 1 is the least element, so if d is in the set, then 1 ≤ d
    intro d hd
    have h : 9 ∣ (437000 + 100 * d + 3) := by 
      simpa using hd
    omega