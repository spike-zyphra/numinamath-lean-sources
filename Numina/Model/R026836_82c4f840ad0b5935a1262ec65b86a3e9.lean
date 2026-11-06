import Mathlib

theorem number_theory_114461 {a b : ℕ} (hb : b ≠ 0) (h1 : a / b = 14) (h2 : a % b = 18)
    (h3 : a - 3 * b = 135) : ∃ m, m^2 = 2 * a := by
  have h4 : a = b * 14 + 18 := by
    rw [←Nat.div_add_mod a b]
    rw [h1, h2]
    all_goals ring
  have h5 : b = 45 := by
    omega
  have h6 : a = 648 := by
    rw [h5] at h4
    omega
  use 36
  rw [h6]
  all_goals norm_num