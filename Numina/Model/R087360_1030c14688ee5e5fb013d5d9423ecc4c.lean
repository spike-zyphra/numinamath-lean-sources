import Mathlib

theorem number_theory_297545 (a b : ℤ) : 3 ∣ a^2 + b^2 → 3 ∣ a ∧ 3 ∣ b := by
  intro h
  -- We need to show both `3 ∣ a` and `3 ∣ b`.
  -- First, let's analyze the residues mod 3 of `a` and `b`
  have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
    omega
  have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
    omega
  rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> 
  ( 
    norm_num [Int.dvd_iff_emod_eq_zero, pow_two, Int.add_emod, Int.mul_emod, h1, h2] at h ⊢
    <;> omega
  )
  all_goals
    omega