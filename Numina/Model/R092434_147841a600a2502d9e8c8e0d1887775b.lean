import Mathlib

theorem number_theory_7935 :
    IsLeast {x : ℚ | ∃ a b : ℕ, x = (10 * a + b) / (a + b) ∧ 1 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9} (19 / 10) := by
  constructor
  · -- Show that 19/10 is obtained when a = 1, b = 9
    use 1, 9
    norm_num
  · -- Show that 19/10 is the minimum value in the set
    intro x h
    rcases h with ⟨a, b, h_eq, ha1, ha2, hb1, hb2⟩

    have h1 : a + b ≠ 0 := by 
      omega

    have h2 : (10 * a + b) / (a + b) ≥ (19 / 10 : ℚ) := by
      have h6 : (a + b : ℚ) > 0 := by
        have ha3 : (a : ℚ) ≥ 1 := by exact_mod_cast ha1
        have hb4 : (b : ℚ) ≥ 0 := by exact_mod_cast hb1
        nlinarith

      have h7 : (9 * (a : ℚ) ≥ (b : ℚ)) := by
        have ha3 : (a : ℚ) ≥ 1 := by exact_mod_cast ha1
        have hb4 : (b : ℚ) ≤ 9 := by exact_mod_cast (show b ≤ 9 by omega)
        nlinarith [show (a : ℚ) ≥ 1 from by exact_mod_cast ha1]

      have h9 : (10 * (a : ℚ) + (b : ℚ)) / (a + b) - (19 / 10 : ℚ) ≥ 0 := by
        have h11 : (10 * (a : ℚ) + (b : ℚ)) / (a + b) - (19 / 10 : ℚ) = 
          (81 * (a : ℚ) - 9 * (b : ℚ)) / (10 * (a + b : ℚ)) := by 
          field_simp
          ring
        rw [h11]
        have h12 : 81 * (a : ℚ) - 9 * (b : ℚ) ≥ 0 := by 
          nlinarith 
        have h13 : 10 * (a + b : ℚ) > 0 := by
          have h14 : (a + b : ℚ) > 0 := h6
          nlinarith
        positivity
      linarith

    rw [h_eq]
    exact_mod_cast h2