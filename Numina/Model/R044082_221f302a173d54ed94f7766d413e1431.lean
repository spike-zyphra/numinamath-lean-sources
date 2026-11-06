import Mathlib

theorem algebra_288892 :
  {x : ℝ | 2 ≤ x ∧ 
   Real.sqrt (x + 2 + 4 * Real.sqrt (x - 2)) +
   Real.sqrt (x + 7 - 6 * Real.sqrt (x - 2)) = 5} =
  {x | 2 ≤ x ∧ x ≤ 11} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First: prove that if x is in left side, it is in right side
    intro h
    rcases h with ⟨hx2, heq⟩
    have h1 : Real.sqrt (x - 2) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h2 : x + 2 + 4 * Real.sqrt (x - 2) = (Real.sqrt (x - 2) + 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith)]
    have h3 : x + 7 - 6 * Real.sqrt (x - 2) = (Real.sqrt (x - 2) - 3) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith)]
    have eq1 : Real.sqrt (x + 2 + 4 * Real.sqrt (x - 2)) = Real.sqrt (x - 2) + 2 := by
      rw [h2]
      have h4 : Real.sqrt ((Real.sqrt (x - 2) + 2) ^ 2) = Real.sqrt (x - 2) + 2 := by
        rw [Real.sqrt_sq]
        linarith [Real.sqrt_nonneg (x - 2)]
      linarith [h4]
    have eq2 : Real.sqrt (x + 7 - 6 * Real.sqrt (x - 2)) = abs (Real.sqrt (x - 2) - 3) := by
      rw [h3]
      have h5 : Real.sqrt ((Real.sqrt (x - 2) - 3) ^ 2) = abs (Real.sqrt (x - 2) - 3) := by
        rw [Real.sqrt_sq_eq_abs]
      linarith [h5]
    rw [eq1, eq2] at heq
    by_cases h4 : Real.sqrt (x - 2) - 3 ≥ 0
    · -- Case 1: If sqrt(x - 2) ≥ 3
      have h5 : abs (Real.sqrt (x - 2) - 3) = Real.sqrt (x - 2) - 3 := by 
        rw [abs_of_nonneg h4]
      rw [h5] at heq
      have h6 : Real.sqrt (x - 2) = 3 := by 
        nlinarith
      have h7 : x - 2 = 9 := by
        calc
          x - 2 = (Real.sqrt (x - 2)) ^ 2 := by 
            rw [Real.sq_sqrt]
            linarith
          _ = (3) ^ 2 := by 
            rw [h6]
          _ = (9 : ℝ) := by 
            norm_num
      have h8 : x = 11 := by linarith
      constructor <;> linarith
    · -- Case 2: If sqrt(x - 2) < 3
      have h5 : abs (Real.sqrt (x - 2) - 3) = 3 - Real.sqrt (x - 2) := by 
        rw [abs_of_neg (show Real.sqrt (x - 2) - 3 < 0 by linarith)]
        all_goals linarith
      rw [h5] at heq
      have h4 : x ≤ 11 := by
        nlinarith [Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith)]
      constructor <;> linarith
  · -- Now the reverse direction: if x in right side, prove it is in left side.
    rintro ⟨hx2, h4⟩
    constructor
    · -- Show x >= 2
      linarith
    · -- Show the equation holds
      have h1 : Real.sqrt (x - 2) ≥ 0 := by
        apply Real.sqrt_nonneg
      have h2 : x + 2 + 4 * Real.sqrt (x - 2) = (Real.sqrt (x - 2) + 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith)]
      have h3 : x + 7 - 6 * Real.sqrt (x - 2) = (Real.sqrt (x - 2) - 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith)]
      have eq1 : Real.sqrt (x + 2 + 4 * Real.sqrt (x - 2)) = Real.sqrt (x - 2) + 2 := by
        rw [h2]
        have h4 : Real.sqrt ((Real.sqrt (x - 2) + 2) ^ 2) = Real.sqrt (x - 2) + 2 := by
          rw [Real.sqrt_sq]
          nlinarith [Real.sqrt_nonneg (x - 2)]
        linarith [h4]
      have eq2 : Real.sqrt (x + 7 - 6 * Real.sqrt (x - 2)) = abs (Real.sqrt (x - 2) - 3) := by
        rw [h3]
        have h5 : Real.sqrt ((Real.sqrt (x - 2) - 3) ^ 2) = abs (Real.sqrt (x - 2) - 3) := by
          rw [Real.sqrt_sq_eq_abs]
        linarith [h5]
      rw [eq1, eq2]
      have h3 : Real.sqrt (x - 2) ≤ 3 := by
        nlinarith [Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith), h4]
      have h7 : abs (Real.sqrt (x - 2) - 3) = 3 - Real.sqrt (x - 2) := by
        rw [abs_of_nonpos (by 
          nlinarith [h3]
        )]
        all_goals linarith
      rw [h7]
      linarith