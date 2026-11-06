import Mathlib

theorem algebra_12385 : IsLeast {x : ℤ | abs (2 * x + 7) ≤ 16} (-11) := by
  constructor 
  · -- Show that -11 is in the set {x : ℤ | abs (2 * x + 7) ≤ 16}
    show abs (2 * (-11) + 7) ≤ 16
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Show that for all y in the set, -11 ≤ y
    intro y hy
    have h : abs (2 * y + 7) ≤ 16 := hy
    rw [abs_le] at h
    linarith