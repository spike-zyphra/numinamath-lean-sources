import Mathlib

theorem number_theory_319685 : ¬∃ x : ℤ, ⌊x⌋ + ⌊2 * x⌋ + ⌊4 * x⌋ + ⌊8 * x⌋ + ⌊16 * x⌋ + ⌊32 * x⌋ = 12345 := by
  rintro ⟨x, hx⟩
  norm_num at hx ⊢
  omega