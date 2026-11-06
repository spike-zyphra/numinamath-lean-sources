import Mathlib

theorem algebra_14023 : {x : ℝ | x > 4 ∧ √(x - 4 * √(x - 4)) + 2 = √(x + 4 * √(x - 4)) - 2} = Set.Ici 8 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · -- Assume x in the left set, prove x in [8, \infty)
    intro h
    rcases h with ⟨hx1, heq⟩
    have h2 : 0 ≤ x - 4 := by linarith
    have h3 : √(x - 4 * √(x - 4)) = abs (√(x - 4) - 2) := by
      have h4 : x - 4 * √(x - 4) = (√(x - 4) - 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show (0 : ℝ) ≤ x - 4 by linarith)]
      rw [h4]
      have h5 : √((√(x - 4) - 2) ^ 2) = abs (√(x - 4) - 2) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h5
    have h4 : √(x + 4 * √(x - 4)) = √(x - 4) + 2 := by
      have h5 : x + 4 * √(x - 4) = (√(x - 4) + 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show (0 : ℝ) ≤ x - 4 by linarith)]
      rw [h5]
      have h6 : √((√(x - 4) + 2) ^ 2) = √(x - 4) + 2 := by
        rw [Real.sqrt_sq (show 0 ≤ √(x - 4) + 2 by positivity)]
      exact h6
    rw [h3, h4] at heq
    have h5 : (√(x - 4) + 2) - 2 = √(x - 4) := by ring
    have heq' : abs (√(x - 4) - 2) + 2 = √(x - 4) := by
      linarith [heq, h5]
    by_cases h6 : √(x - 4) - 2 ≥ 0
    · -- case1 : √(x - 4) - 2 ≥ 0
      rw [abs_of_nonneg h6] at heq'
      have h7 : √(x - 4) ≥ 2 := by linarith
      have h8 : x - 4 ≥ 4 := by
        nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show (0 : ℝ) ≤ x - 4 by linarith), h7]
      have h9 : x ≥ 8 := by linarith
      linarith
    · -- case2 : √(x - 4) - 2 < 0
      rw [abs_of_neg (show √(x - 4) - 2 < 0 by linarith)] at heq'
      have heq'' : 4 - √(x - 4) = √(x - 4) := by
        nlinarith
      have h10 : √(x - 4) = 2 := by
        nlinarith
      have h11 : x - 4 = 4 := by
        calc
          x - 4 = (Real.sqrt (x - 4)) ^ 2 := by
            rw [Real.sq_sqrt]
            linarith
          _ = (2 : ℝ) ^ 2 := by
            rw [h10]
          _ = (4 : ℝ) := by
            norm_num
      have h12 : x = 8 := by linarith
      linarith
  · -- Assume x in [8, \infty), prove x in the left set
    intro h
    constructor
    · -- Show x > 4
      nlinarith
    · -- Show the equation
      have h14 : x ≥ 8 := by linarith
      have h2 : 0 ≤ x - 4 := by linarith
      have h3 : √(x - 4 * √(x - 4)) = abs (√(x - 4) - 2) := by
        have h4 : x - 4 * √(x - 4) = (√(x - 4) - 2) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show (0 : ℝ) ≤ x - 4 by linarith)]
        rw [h4]
        have h5 : √((√(x - 4) - 2) ^ 2) = abs (√(x - 4) - 2) := by
          rw [Real.sqrt_sq_eq_abs]
        exact h5
      have h4 : √(x + 4 * √(x - 4)) = √(x - 4) + 2 := by
        have h5 : x + 4 * √(x - 4) = (√(x - 4) + 2) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show (0 : ℝ) ≤ x - 4 by linarith)]
        rw [h5]
        have h6 : √((√(x - 4) + 2) ^ 2) = √(x - 4) + 2 := by
          rw [Real.sqrt_sq (show 0 ≤ √(x - 4) + 2 by positivity)]
        exact h6
      have h5 : √(x - 4) ≥ 2 := by
        have h15 : x - 4 ≥ 4 := by
          nlinarith
        have h16 : √(x - 4) ≥ √(4 : ℝ) := by
          apply Real.sqrt_le_sqrt
          linarith
        have h17 : √(4 : ℝ) = (2 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        nlinarith [h17, h16, Real.sqrt_nonneg (4 : ℝ), Real.sqrt_nonneg (x - 4)]
      rw [h3, h4]
      have h5' : (√(x - 4) + 2) - 2 = √(x - 4) := by ring
      rw [h5']
      have h58 : √(x - 4) - (2 : ℝ) ≥ 0 := by
        nlinarith [h5, Real.sqrt_nonneg (x - 4)]
      rw [abs_of_nonneg h58]
      all_goals nlinarith