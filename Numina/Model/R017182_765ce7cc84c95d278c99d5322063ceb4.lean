import Mathlib

theorem number_theory_176537 (p q : ℕ) (hp : 0 < p) (hq : p < q) :
    (p / q : ℝ) < 1 ∧ 1 < (q / p : ℝ) ∧ |(p / q : ℝ) - 1| < |(q / p : ℝ) - 1| := by

  have h1 : (p : ℝ) > 0 := by
    exact_mod_cast (show (p : ℕ) > 0 by linarith)
  have h2 : (q : ℝ) > 0 := by
    have hq' : (q : ℕ) > 0 := by
      linarith
    exact_mod_cast hq'

  have h3 : (p : ℝ) < (q : ℝ) := by
    exact_mod_cast (show (p : ℕ) < (q : ℕ) by linarith)

  have h4 : (p / q : ℝ) < 1 := by
    have h5 : (p : ℝ) < (q : ℝ) := h3
    have h6 : (q : ℝ) > 0 := h2
    have h7 : (p / q : ℝ) < (q / q : ℝ) := by
      apply (div_lt_div_right h6).mpr
      linarith
    have h8 : (q / q : ℝ) = 1 := by
      field_simp [show (q : ℝ) ≠ 0 by linarith]
    linarith [h7, h8]

  have h5 : 1 < (q / p : ℝ) := by
    have h8 : (p : ℝ) < (q : ℝ) := h3
    have h9 : (p : ℝ) > 0 := h1
    have h10 : (q / p : ℝ) > (p / p : ℝ) := by
      apply (div_lt_div_right h9).mpr
      linarith
    have h11 : (p / p : ℝ) = 1 := by
      field_simp [show (p : ℝ) ≠ 0 by linarith]
    linarith [h10, h11]

  constructor
  · exact h4
  constructor
  · exact h5

  have h8 : |(p / q : ℝ) - 1| = 1 - (p / q : ℝ) := by
    rw [abs_of_neg]
    linarith
    all_goals linarith

  have h9 : |(q / p : ℝ) - 1| = (q / p : ℝ) - 1 := by
    rw [abs_of_pos]
    linarith
    all_goals linarith

  rw [h8, h9]

  have h13 : 1 - (p / q : ℝ) < (q / p : ℝ) - 1 := by
    have h14 : (1 - (p / q : ℝ) : ℝ) - ((q / p : ℝ) - 1) < 0 := by
      have h15 : (1 - (p / q : ℝ) : ℝ) - ((q / p : ℝ) - 1) = 2 - (p / q : ℝ) - (q / p : ℝ) := by
        linarith
      rw [h15]
      have h16 : 2 - (p / q : ℝ) - (q / p : ℝ) < 0 := by
        have h17 : 2 - (p / q : ℝ) - (q / p : ℝ) = (2 * (p * (q) ) - p ^ 2 - q ^ 2) / ( (q) * (p) ) := by
          field_simp
          <;> ring
        rw [h17]
        apply div_neg_of_neg_of_pos
        · -- Show that 2 * (p * (q) ) - p ^ 2 - q ^ 2 < 0
          have h18 : (2 * (p * (q) ) - p ^ 2 - q ^ 2 : ℝ) < 0 := by
            have h19 : (p : ℝ) < (q : ℝ) := h3
            nlinarith [sq_pos_of_pos h1, sq_pos_of_pos h2, mul_pos h1 h2, sq_pos_of_pos (show (0 : ℝ) < (q - p : ℝ) by 
              have : (q : ℝ) > (p : ℝ) := by linarith
              nlinarith
            )]
          linarith
        · -- Show that (q * p) > 0
          positivity
      linarith

    linarith

  linarith [h13]