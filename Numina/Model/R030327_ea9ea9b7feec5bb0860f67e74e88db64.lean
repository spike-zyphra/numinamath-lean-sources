import Mathlib

theorem algebra_258683 :
    ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ Irrational x ∧ Irrational y ∧ ¬Irrational (x + y) ∧ ¬Irrational (x * y) := by 
  use 3 - Real.sqrt 2, 3 + Real.sqrt 2
  have h1 : (3 - Real.sqrt 2 : ℝ) + (3 + Real.sqrt 2 : ℝ) = (6 : ℝ) := by 
    ring_nf 
  have h2 : (3 - Real.sqrt 2 : ℝ) * (3 + Real.sqrt 2 : ℝ) = (7 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  constructor 
  · -- Show x > 0 
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 - 3 : ℝ), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  constructor
  · -- Show y > 0 
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 + 3 : ℝ), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  constructor
  · -- Show x is irrational 
    have h3 : Irrational (3 - Real.sqrt 2 : ℝ) := by 
      have h4 : Irrational (Real.sqrt 2 : ℝ) := by 
        apply irrational_sqrt_two 
      intro h 
      have h5 : ¬ Irrational (Real.sqrt 2 : ℝ) := by 
        rcases h with ⟨a, ha⟩ 
        set q := (a : ℚ) 
        have h6 : (Real.sqrt 2 : ℝ) = ( (3 : ℝ) - ↑q ) := by 
          linarith 
        rw [h6]
        simp 
      contradiction 
    simpa using h3 
  constructor
  · -- Show y is irrational 
    have h4 : Irrational (3 + Real.sqrt 2 : ℝ) := by 
      have h5 : Irrational (Real.sqrt 2 : ℝ) := by 
        apply irrational_sqrt_two 
      intro h 
      have h6 : ¬ Irrational (Real.sqrt 2 : ℝ) := by 
        rcases h with ⟨a, ha⟩ 
        set q := (a : ℚ) 
        have h7 : (Real.sqrt 2 : ℝ) = (↑q - (3 : ℝ) ) := by 
          linarith 
        rw [h7]
        simp 
      contradiction 
    simpa using h4 
  constructor
  · -- Show x + y is not irrational 
    rw [h1] 
    have h8 : ¬ Irrational (6 : ℝ) := by 
      simp [Irrational]
      use (6 : ℤ)
      norm_num 
    simpa using h8 
  · -- Show x * y is not irrational 
    rw [h2] 
    have h9 : ¬ Irrational (7 : ℝ) := by 
      simp [Irrational]
      use (7 : ℤ)
      norm_num 
    simpa using h9