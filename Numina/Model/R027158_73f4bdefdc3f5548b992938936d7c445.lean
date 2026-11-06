import Mathlib

theorem number_theory_3918 : IsGreatest {x | x % 101 = (Nat.factorial 50) ^ 2020 % 101 ∧ x < 10000} 9899 := by
  constructor
  · -- Show 9899 is in the set
    constructor
    · -- Show that 9899 % 101 = (Nat.factorial 50) ^ 2020 % 101
      native_decide
    · -- Show that 9899 < 10000
      norm_num
  · -- Show that 9899 is greatest in the set
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have h1 : x % 101 = (Nat.factorial 50) ^ 2020 % 101 := hx1
    have h2 : (Nat.factorial 50) ^ 2020 % 101 = 1 := by
      native_decide
    have h3 : x % 101 = 1 := by
      rw [h2] at h1
      exact h1
    omega