import Mathlib

theorem algebra_12879 (a : ℕ → ℤ) (ha : ∀ n, a n = 88 - 3 * n) :
    IsLeast {n | ∃ k, a n = -17 ∧ k = n} 35 := by 
  constructor 
  · -- Show that 35 is in the set.
    use 35
    constructor
    · -- Show that a 35 = -17
      rw [ha 35]
      all_goals norm_num 
    · -- Trivial equality
      rfl
  · -- Show that 35 is minimal in the set
    intro n hn
    rcases hn with ⟨k, hk1, hk2⟩
    have h_eq : a n = -17 := by
      tauto 
    rw [ha n] at h_eq
    omega