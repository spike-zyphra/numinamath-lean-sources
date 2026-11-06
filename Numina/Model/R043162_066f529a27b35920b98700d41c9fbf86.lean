import Mathlib

theorem algebra_46055 (a b : ℤ) (_ : 0 < a) (h₁ : 0 < b) :
    ∃ x y : ℤ, 0 < x ∧ 0 < y ∧ (x / (y + a : ℝ) + y / (x + b : ℝ) = 3 / 2) := by

  use 2 * a + b, a + b

  constructor
  · -- Show that x > 0
    have h3 : (2 * a + b : ℤ) > (0 : ℤ) := by
      have h2' : (a : ℤ) > 0 := by linarith
      have h2'' : (b : ℤ) > 0 := by linarith
      omega
    exact_mod_cast h3

  constructor
  · -- Show that y > 0
    have h5 : (a + b : ℤ) > (0 : ℤ) := by
      have h2' : (a : ℤ) > 0 := by linarith
      have h2'' : (b : ℤ) > 0 := by linarith
      omega
    exact_mod_cast h5

  · -- Verify that the equation holds
    have eq1 : ((2 * a + b : ℝ) / ((a + b : ℝ) + (a : ℝ)) + ( (a + b : ℝ) / ((2 * a + b : ℝ) + (b : ℝ)) ) = 3 / 2) := by
      have hx1 : ( (2 * a + b : ℝ) / ( (a + b : ℝ) + (a : ℝ) ) ) = 1 := by
        have hx2 : ( (a + b : ℝ) + (a : ℝ) ) = (2 * a + b : ℝ) := by ring
        rw [hx2]
        have hx4 : (2 * a + b : ℝ) ≠ 0 := by
          have h2 : (2 * a + b : ℝ) > (0 : ℝ) := by
            have ha : (a : ℝ) > (0 : ℝ) := by exact_mod_cast (show 0 < (a : ℤ) by linarith)
            have hb : (b : ℝ) > (0 : ℝ) := by exact_mod_cast (show 0 < (b : ℤ) by linarith)
            linarith
          linarith
        field_simp [hx4]
        <;> nlinarith

      have hx2 : ( ( (a + b : ℝ) ) / ( ( (2 * a + b : ℝ) ) + (b : ℝ) ) ) = 1 / 2 := by
        have hx3 : ( (2 * a + b : ℝ) + (b : ℝ) ) = 2 * ( (a + b : ℝ) ) := by
          ring_nf
        rw [hx3]
        have hx4 : (a + b : ℝ) > 0 := by
          have ha : (a : ℝ) > (0 : ℝ) := by exact_mod_cast (show 0 < (a : ℤ) by linarith)
          have hb : (b : ℝ) > (0 : ℝ) := by exact_mod_cast (show 0 < (b : ℤ) by linarith)
          linarith
        have hx5 : (a + b : ℝ) ≠ 0 := by linarith
        field_simp [hx5]
        <;> nlinarith
      rw [hx1, hx2]
      all_goals linarith

    simpa using eq1