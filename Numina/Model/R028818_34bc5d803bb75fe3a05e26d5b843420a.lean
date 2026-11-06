import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_197517 : {x : ℝ | x ≥ 1 ∧ sqrt (x + 3 - 4 * sqrt (x - 1)) + sqrt (x + 8 - 6 * sqrt (x - 1)) = 1 } = Set.Icc 5 10 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Assume h : x ∈ {x : ℝ | x ≥ 1 ∧ sqrt (x + 3 - 4 * sqrt (x - 1)) + sqrt (x + 8 - 6 * sqrt (x - 1)) = 1 }
    intro h
    rcases h with ⟨hx1, heq⟩
    have h2 : x - 1 ≥ 0 := by linarith
    have h3 : sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
    
    have eq1 : x + 3 - 4 * sqrt (x - 1) = (sqrt (x - 1) - 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]
    
    have eq2 : x + 8 - 6 * sqrt (x - 1) = (sqrt (x - 1) - 3) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]

    have eq3 : sqrt (x + 3 - 4 * sqrt (x - 1)) = abs (sqrt (x - 1) - 2) := by
      rw [eq1]
      have h4 : sqrt ((sqrt (x - 1) - 2) ^ 2) = abs (sqrt (x - 1) - 2) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h4

    have eq4 : sqrt (x + 8 - 6 * sqrt (x - 1)) = abs (sqrt (x - 1) - 3) := by
      rw [eq2]
      have h5 : sqrt ((sqrt (x - 1) - 3) ^ 2) = abs (sqrt (x - 1) - 3) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h5

    rw [eq3, eq4] at heq

    have h4 : 2 ≤ sqrt (x - 1) ∧ sqrt (x - 1) ≤ 3 := by 
      constructor
      · -- Show that 2 ≤ sqrt (x - 1)
        cases' abs_cases (sqrt (x - 1) - 2) with h h <;> 
          cases' abs_cases (sqrt (x - 1) - 3) with k k <;> 
            try { 
              nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]
            }
      · -- Show that sqrt (x - 1) ≤ 3
        cases' abs_cases (sqrt (x - 1) - 2) with h h <;> 
          cases' abs_cases (sqrt (x - 1) - 3) with k k <;> 
            try { 
              nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]
            }

    have hx2 : 4 ≤ x - 1 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith), h4.1]

    have hx3 : x - 1 ≤ 9 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith), h4.2]

    constructor
    · linarith
    · linarith

  · -- Assume h : x ∈ [5, 10]
    rintro ⟨hx1, hx2⟩
    constructor
    · -- Show x ≥ 1
      linarith
    · -- Show sqrt (x + 3 - 4 * sqrt (x - 1)) + sqrt (x + 8 - 6 * sqrt (x - 1)) = 1
      have h2 : x - 1 ≥ 0 := by linarith
      have h3 : sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
    
      have eq1 : x + 3 - 4 * sqrt (x - 1) = (sqrt (x - 1) - 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]
    
      have eq2 : x + 8 - 6 * sqrt (x - 1) = (sqrt (x - 1) - 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]

      have eq3 : sqrt (x + 3 - 4 * sqrt (x - 1)) = abs (sqrt (x - 1) - 2) := by
        rw [eq1]
        have h4 : sqrt ((sqrt (x - 1) - 2) ^ 2) = abs (sqrt (x - 1) - 2) := by
          rw [Real.sqrt_sq_eq_abs]
        exact h4

      have eq4 : sqrt (x + 8 - 6 * sqrt (x - 1)) = abs (sqrt (x - 1) - 3) := by
        rw [eq2]
        have h5 : sqrt ((sqrt (x - 1) - 3) ^ 2) = abs (sqrt (x - 1) - 3) := by
          rw [Real.sqrt_sq_eq_abs]
        exact h5

      -- Show that 2 ≤ sqrt (x - 1) ≤ 3
      have h4 : 2 ≤ sqrt (x - 1) ∧ sqrt (x - 1) ≤ 3 := by 
        constructor
        · -- Show that 2 ≤ sqrt (x - 1)
          nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]
        · -- Show that sqrt (x - 1) ≤ 3
          nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]

      have h6 : abs (sqrt (x - 1) - 2) = sqrt (x - 1) - 2 := by
        rw [abs_of_nonneg]
        nlinarith [Real.sqrt_nonneg (x - 1)]
    
      have h7 : abs (sqrt (x - 1) - 3) = 3 - sqrt (x - 1) := by
        rw [abs_of_nonpos]
        all_goals nlinarith [Real.sqrt_nonneg (x - 1)]

      rw [eq3, eq4]
      rw [h6, h7]
      nlinarith [Real.sqrt_nonneg (x - 1)]