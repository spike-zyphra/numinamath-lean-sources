import Mathlib

theorem algebra_231835 (a b : ℕ) (ha : a = 12) (hb : b = 8) :
    IsLeast {x | 100 ≤ a * x + b * x} 5 := by 
  rw [ha, hb]
  constructor 
  · -- Show that 5 is indeed in the set
    norm_num 
  · -- We need to show that 5 is the smallest element
    intro x h 
    have h1 : 100 ≤ 12 * x + 8 * x := h 
    by_contra h2 
    push_neg at h2 
    have h3 : x < 5 := by omega 
    interval_cases x <;> omega