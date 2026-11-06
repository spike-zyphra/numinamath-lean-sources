import Mathlib.Tactic

theorem number_theory_123162 (m : ℕ) (hm : 0 < m) (a b : ℤ)
    (hcoprime : IsCoprime a b) (hdiv1 : a ∣ m + b^2) (hdiv2 : b ∣ m + a^2) :
    ∃ a' b' : ℤ, 0 < a' ∧ 0 < b' ∧ a' + b' ≤ m + 1 ∧ IsCoprime a' b' ∧ a' ∣ m + b'^2 ∧ b' ∣ m + a'^2 := by

  use 1, 1
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · -- Show that 1 + 1 ≤ m + 1
    have h1 : (m : ℤ) ≥ 1 := by exact_mod_cast Nat.one_le_of_lt hm
    omega
  constructor
  · -- Show that IsCoprime 1 1
    norm_num
  constructor
  · -- Show that 1 divides m + 1^2
    norm_num
    all_goals try { omega }
  · -- Show that 1 divides m + 1^2
    norm_num
    all_goals try { omega }