import Mathlib

theorem inequalities_114447 (n : ℕ) (hn : 0 < n) :
    (1 + 3 / (n + 1) : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < (1 + 3 / n : ℝ) ↔ n = 4 := by
  constructor
  · -- Assume (1 + 3 / (n + 1) : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < (1 + 3 / n : ℝ), prove n = 4
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : (n : ℝ) > 0 := by
      exact_mod_cast show (0 : ℝ) < (n : ℝ) by exact_mod_cast (show 0 < n by linarith)
    by_cases h9 : n > 4
    · -- Assume n > 4, need to derive contradiction
      have h10 : n ≥ 5 := by
        omega
      have h10' : (n : ℝ) ≥ (5 : ℝ) := by exact_mod_cast h10
      have h11 : Real.sqrt 3 < (1 + 3 / (n : ℝ) : ℝ) := h2
      have h12 : (n : ℝ) * (Real.sqrt 3 - 1) < (3 : ℝ) := by
        have h13 : Real.sqrt 3 < (1 + 3 / (n : ℝ) : ℝ) := h2
        have h14 : (Real.sqrt 3 : ℝ) - 1 < (3 / (n : ℝ) : ℝ) := by linarith
        have h15 : (n : ℝ) > 0 := by
          have : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast show n ≥ 1 by linarith
          nlinarith
        have h16 : (n : ℝ) * ((Real.sqrt 3 : ℝ) - 1) < (3 : ℝ) := by
          have h17 : (Real.sqrt 3 : ℝ) - 1 < (3 / (n : ℝ) : ℝ) := h14
          have h18 : (n : ℝ) * ((Real.sqrt 3 : ℝ) - 1) < (n : ℝ) * (3 / (n : ℝ) : ℝ) := by
            apply mul_lt_mul_of_pos_left
            linarith
            positivity
          have h19 : (n : ℝ) * (3 / (n : ℝ) : ℝ) = (3 : ℝ) := by
            field_simp
          linarith
        linarith
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        Real.sqrt_nonneg (3 : ℝ)]
    · -- Assume n ≤ 4
      have h10 : n ≤ 4 := by
        omega
      -- Then since 0 < n ≤ 4, so n = 1, 2, 3, 4
      have h11 : n > 0 := by linarith
      have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
        interval_cases n <;> tauto
      rcases this with (r | r | r | r)
      · -- n = 1
        have h14 : n = 1 := r
        rw [show (n : ℝ) = (1 : ℝ) by exact_mod_cast h14] at h1 h2
        norm_num at h1 h2
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sqrt_nonneg (3 : ℝ)]
      · -- n = 2
        have h14 : n = 2 := r
        rw [show (n : ℝ) = (2 : ℝ) by exact_mod_cast h14] at h1 h2
        norm_num at h1 h2
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sqrt_nonneg (3 : ℝ)]
      · -- n = 3
        have h14 : n = 3 := r
        rw [show (n : ℝ) = (3 : ℝ) by exact_mod_cast h14] at h1 h2
        norm_num at h1 h2
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sqrt_nonneg (3 : ℝ)]
      · -- n = 4
        have h14 : n = 4 := r
        exact h14
  · -- Assume n = 4, prove (1 + 3 / (n + 1) : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < (1 + 3 / n : ℝ)
    intro h
    have h10 : n = 4 := h
    rw [show (n : ℝ) = (4 : ℝ) by exact_mod_cast h10]
    constructor
    · -- Show 1 + 3/5 < Real.sqrt 3
      have h14 : (1 + (3 / ((4 : ℝ) + 1) : ℝ) : ℝ) < Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sqrt_nonneg (3 : ℝ), 
          sq_nonneg (Real.sqrt 3 - (1.732 : ℝ)), 
          sq_nonneg (Real.sqrt 3 ^ 2 - 3)]
      norm_num at h14 ⊢
      all_goals nlinarith
    · -- Show Real.sqrt 3 < 1 + 3/4
      have h14 : Real.sqrt 3 < (1 + 3 / (4 : ℝ) : ℝ) := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sqrt_nonneg (3 : ℝ), 
          sq_nonneg (Real.sqrt 3 - (1.732 : ℝ)), 
          sq_nonneg (Real.sqrt 3 ^ 2 - 3)]
      norm_num at h14 ⊢
      all_goals nlinarith