import Mathlib

theorem number_theory_174865 :
    IsGreatest {x : ℚ | ∃ a b : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ a < 100 ∧ b < 100 ∧ a ≠ b ∧ x = (a - b) / (a + b)} (49 / 50) := by
  constructor
  · -- Show that 49/50 is in the set
    use 99, 1
    all_goals norm_num
  · -- Show that 49/50 is the greatest
    intro x hx
    rcases hx with ⟨a, b, ha, hb, ha100, hb100, hab, hx⟩
    by_cases h : a < b
    · -- Assume that a < b, so a - b < 0, so x < 0.
      have h6 : (a : ℚ) < (b : ℚ) := by exact_mod_cast h
      have hx1 : x = (a - b : ℚ) / (a + b : ℚ) := by
        linarith [hx]
      have hx2 : x ≤ (0 : ℚ) := by
        rw [hx1]
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Show that (a : ℚ) - (b : ℚ) ≤ 0.
          have h1 : (a : ℚ) < (b : ℚ) := by exact_mod_cast h
          linarith
        · -- Show that (a + b : ℚ) ≥ 0.
          have h3 : (a : ℚ) > (0 : ℚ) := by
            have h1 : a ≠ 0 := ha
            have h2 : a ≥ 1 := by omega
            exact_mod_cast (show a > 0 by omega)
          have h4 : (b : ℚ) > (0 : ℚ) := by
            have h1 : b ≠ 0 := hb
            have h2 : b ≥ 1 := by omega
            exact_mod_cast (show b > 0 by omega)
          have h5 : (a + b : ℚ) > (0 : ℚ) := by positivity
          linarith
      have hx3 : x ≤ (49 / 50 : ℚ) := by
        linarith [hx2]
      linarith
    · -- Case a ≥ b
      have leq1 : a ≥ b := by omega
      have hx1 : x = (a - b : ℚ) / (a + b : ℚ) := by
        linarith [hx]
      have h41 : ((a - b : ℚ) / (a + b : ℚ)) ≤ (49 / 50 : ℚ) := by
        have h7 : (a + b : ℚ) > 0 := by
          have h3 : (a : ℚ) > (0 : ℚ) := by
            have h1 : a ≠ 0 := ha
            have h2 : a ≥ 1 := by omega
            exact_mod_cast (show a > 0 by omega)
          have h4 : (b : ℚ) > (0 : ℚ) := by
            have h1 : b ≠ 0 := hb
            have h2 : b ≥ 1 := by omega
            exact_mod_cast (show b > 0 by omega)
          linarith
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        suffices 50 * (a : ℚ) - 50 * (b : ℚ) ≤ 49 * (a : ℚ) + 49 * (b : ℚ) by
          linarith
        -- Prove cross multiplied.
        have h6 : a ≤ 99 * b := by
          have ha100 : a < 100 := by omega
          have h7 : b ≥ 1 := by omega
          have h8 : a ≤ 99 := by omega
          omega
        have h7 : (a : ℚ) ≤ 99 * (b : ℚ) := by
          exact_mod_cast h6
        linarith
      rw [hx1]
      linarith