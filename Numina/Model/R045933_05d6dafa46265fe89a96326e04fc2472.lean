import Mathlib.Tactic

theorem number_theory_149153 (a : Fin 5 → ℤ) : ∃ b c d, b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ 3 ∣ a b + a c + a d := by

  have h2 : ∀ x : ℤ, x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by 
    omega

  have h3 : a 0 % 3 = 0 ∨ a 0 % 3 = 1 ∨ a 0 % 3 = 2 := h2 (a 0)
  have h4 : a 1 % 3 = 0 ∨ a 1 % 3 = 1 ∨ a 1 % 3 = 2 := h2 (a 1)
  have h5 : a 2 % 3 = 0 ∨ a 2 % 3 = 1 ∨ a 2 % 3 = 2 := h2 (a 2)
  have h6 : a 3 % 3 = 0 ∨ a 3 % 3 = 1 ∨ a 3 % 3 = 2 := h2 (a 3)
  have h7 : a 4 % 3 = 0 ∨ a 4 % 3 = 1 ∨ a 4 % 3 = 2 := h2 (a 4)

  have h9 : (a 0 + a 1 + a 2) % 3 = 0 ∨ (a 0 + a 1 + a 3) % 3 = 0 ∨ (a 0 + a 1 + a 4) % 3 = 0 ∨ (a 0 + a 2 + a 3) % 3 = 0 ∨ (a 0 + a 2 + a 4) % 3 = 0 ∨ (a 0 + a 3 + a 4) % 3 = 0 ∨ (a 1 + a 2 + a 3) % 3 = 0 ∨ (a 1 + a 2 + a 4) % 3 = 0 ∨ (a 1 + a 3 + a 4) % 3 = 0 ∨ (a 2 + a 3 + a 4) % 3 = 0 := by 
    omega

  rcases h9 with (h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9)

  · 
    use 0, 1, 2
    all_goals
      constructor
      · -- Show that 0 ≠ 1
        simp
      constructor
      · -- Show that 0 ≠ 2
        simp
      constructor
      · -- Show that 1 ≠ 2
        simp
      · -- Show that 3 divides a 0 + a 1 + a 2
        omega

  · 
    use 0, 1, 3
    all_goals
      constructor
      · -- Show that 0 ≠ 1
        simp
      constructor
      · -- Show that 0 ≠ 3
        simp
      constructor
      · -- Show that 1 ≠ 3
        simp
      · -- Show that 3 divides a 0 + a 1 + a 3
        omega

  · 
    use 0, 1, 4
    all_goals
      constructor
      · -- Show that 0 ≠ 1
        simp
      constructor
      · -- Show that 0 ≠ 4
        simp
      constructor
      · -- Show that 1 ≠ 4
        simp
      · -- Show that 3 divides a 0 + a 1 + a 4
        omega

  · 
    use 0, 2, 3
    all_goals
      constructor
      · -- Show that 0 ≠ 2
        simp
      constructor
      · -- Show that 0 ≠ 3
        simp
      constructor
      · -- Show that 2 ≠ 3
        simp
      · -- Show that 3 divides a 0 + a 2 + a 3
        omega

  · 
    use 0, 2, 4
    all_goals
      constructor
      · -- Show that 0 ≠ 2
        simp
      constructor
      · -- Show that 0 ≠ 4
        simp
      constructor
      · -- Show that 2 ≠ 4
        simp
      · -- Show that 3 divides a 0 + a 2 + a 4
        omega

  · 
    use 0, 3, 4
    all_goals
      constructor
      · -- Show that 0 ≠ 3
        simp
      constructor
      · -- Show that 0 ≠ 4
        simp
      constructor
      · -- Show that 3 ≠ 4
        simp
      · -- Show that 3 divides a 0 + a 3 + a 4
        omega

  · 
    use 1, 2, 3
    all_goals
      constructor
      · -- Show that 1 ≠ 2
        simp
      constructor
      · -- Show that 1 ≠ 3
        simp
      constructor
      · -- Show that 2 ≠ 3
        simp
      · -- Show that 3 divides a 1 + a 2 + a 3
        omega

  · 
    use 1, 2, 4
    all_goals
      constructor
      · -- Show that 1 ≠ 2
        simp
      constructor
      · -- Show that 1 ≠ 4
        simp
      constructor
      · -- Show that 2 ≠ 4
        simp
      · -- Show that 3 divides a 1 + a 2 + a 4
        omega

  · 
    use 1, 3, 4
    all_goals
      constructor
      · -- Show that 1 ≠ 3
        simp
      constructor
      · -- Show that 1 ≠ 4
        simp
      constructor
      · -- Show that 3 ≠ 4
        simp
      · -- Show that 3 divides a 1 + a 3 + a 4
        omega

  · 
    use 2, 3, 4
    all_goals
      constructor
      · -- Show that 2 ≠ 3
        simp
      constructor
      · -- Show that 2 ≠ 4
        simp
      constructor
      · -- Show that 3 ≠ 4
        simp
      · -- Show that 3 divides a 2 + a 3 + a 4
        omega