import Mathlib

theorem number_theory_114159 (a : ℕ) :
    ∃ x : ℚ, |(a : ℝ) - Real.sqrt 2| + |(a : ℝ) - 2 * Real.sqrt 2| +
      |(a : ℝ) - 3 * Real.sqrt 2| = x ↔ a = 3 := by

  by_cases h3a : a = 3
  · -- Case a = 3
    use (3 : ℚ)
    have h4 : (a : ℝ) = (3 : ℝ) := by
      exact_mod_cast h3a
    have h5 : |(a : ℝ) - Real.sqrt 2| + |(a : ℝ) - 2 * Real.sqrt 2| +
        |(a : ℝ) - 3 * Real.sqrt 2| = (3 : ℝ) := by
      rw [show (a : ℝ) = (3 : ℝ) by exact_mod_cast h3a]
      have h41 : |(3 : ℝ) - Real.sqrt 2| = (3 - Real.sqrt 2 : ℝ) := by 
        rw [abs_of_nonneg]
        linarith [show Real.sqrt 2 ≤ (3 : ℝ) by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num) ] ]
      have h42 : |(3 : ℝ) - 2 * Real.sqrt 2| = (3 - 2 * Real.sqrt 2 : ℝ) := by 
        rw [abs_of_nonneg]
        linarith [show 2 * Real.sqrt 2 ≤ (3 : ℝ) by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num) ] ]
      have h43 : |(3 : ℝ) - 3 * Real.sqrt 2| = (3 * Real.sqrt 2 - 3 : ℝ) := by 
        rw [abs_of_nonpos]
        · linarith [show (3 : ℝ) ≤ 3 * Real.sqrt 2 by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num) ] ]
        all_goals linarith [show (3 : ℝ) ≤ 3 * Real.sqrt 2 by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num) ] ]
      rw [h41, h42, h43]
      linarith
    constructor
    · -- Forward: if LHS = ↑x, then a = 3
      intro h_eq
      norm_num [h5] at h_eq ⊢
      all_goals tauto
    · -- Backward: a = 3 → LHS = ↑x
      intro h_eq
      rw [show (a : ℝ) = (3 : ℝ) by exact_mod_cast h_eq] at *
      norm_num [h5] at *
      all_goals tauto

  · -- Case a ≠ 3
    use (0 : ℚ)
    constructor
    · -- Forward: if LHS = ↑0, then a = 3
      intro h_eq
      have eq1 : |(a : ℝ) - Real.sqrt 2| + |(a : ℝ) - 2 * Real.sqrt 2| + |(a : ℝ) - 3 * Real.sqrt 2| = (0 : ℝ) := by
        norm_num at h_eq ⊢
        exact_mod_cast h_eq
      have h8 : |(a : ℝ) - Real.sqrt 2| ≥ 0 := by apply abs_nonneg
      have h9 : |(a : ℝ) - 2 * Real.sqrt 2| ≥ 0 := by apply abs_nonneg
      have h10 : |(a : ℝ) - 3 * Real.sqrt 2| ≥ 0 := by apply abs_nonneg
      have h11 : |(a : ℝ) - Real.sqrt 2| = 0 := by
        linarith
      have h12 : (a : ℝ) = Real.sqrt 2 := by
        rw [abs_eq_zero] at h11
        linarith
      have h14 : Irrational (Real.sqrt 2) := by 
        native_decide
      have h13 : ¬ Irrational ((a : ℝ)) := by
        simp [Irrational]
        <;> try { 
          use (a : ℚ)
          all_goals norm_num 
        }
      -- Contradiction
      have h16 : Irrational ((a : ℝ)) := by 
        rw [h12]
        exact h14
      contradiction
    · -- Backward: a = 3 → LHS = ↑0
      intro h_eq
      exfalso
      tauto