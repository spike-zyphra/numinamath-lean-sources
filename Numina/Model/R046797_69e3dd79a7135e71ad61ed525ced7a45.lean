import Mathlib


theorem algebra_279700 :
  {x : ℝ | x ≥ 0 ∧ 11 * x - x ^ 2 = 24 - 2 * Real.sqrt x} = {9, (9 - Real.sqrt 17) / 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x ≥ 0 and 11 * x - x ^ 2 = 24 - 2 * Real.sqrt x, prove x = 9 ∨ x = (9 - Real.sqrt 17) / 2
    intro h
    rcases h with ⟨hx0, heq⟩
    have h1 : 0 ≤ Real.sqrt x := by positivity
    have h2 : Real.sqrt x ^ 2 = x := by
      rw [Real.sq_sqrt]
      linarith
    have h3 : Real.sqrt x ^ 4 - 11 * Real.sqrt x ^ 2 - 2 * Real.sqrt x + 24 = 0 := by
      nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x ^ 2 - 9), sq_nonneg (Real.sqrt x ^ 2 - (9 - Real.sqrt 17) / 2), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
    have h4 : (Real.sqrt x - 3) * (Real.sqrt x + 2) * (Real.sqrt x ^ 2 + Real.sqrt x - 4) = 0 := by
      nlinarith [sq_nonneg (Real.sqrt x ^ 2 - 9), sq_nonneg (Real.sqrt x ^ 2 - (9 - Real.sqrt 17) / 2), Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x ^ 2 - (9 - Real.sqrt 17) / 2)]
    cases' (mul_eq_zero.1 h4) with h5 h6
    cases' (mul_eq_zero.1 h5) with h7 h8
    · -- Real.sqrt x - 3 = 0
      have h8 : Real.sqrt x = 3 := by linarith
      have h9 : x = 9 := by
        calc
          x = Real.sqrt x ^ 2 := by
            rw [Real.sq_sqrt]
            linarith
          _ = 3 ^ 2 := by
            rw [h8]
          _ = 9 := by norm_num
      left
      linarith
    · -- Real.sqrt x + 2 = 0
      nlinarith [Real.sqrt_nonneg x]
    · -- Real.sqrt x ^ 2 + Real.sqrt x - 4 = 0
      have h7 : Real.sqrt x ^ 2 + Real.sqrt x - 4 = 0 := by nlinarith
      have h8 : Real.sqrt x = (-1 + Real.sqrt 17) / 2 := by
        nlinarith [sq_nonneg (Real.sqrt x), Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
      have h9 : x = (9 - Real.sqrt 17) / 2 := by
        nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), sq_nonneg (Real.sqrt x - (-1 + Real.sqrt 17) / 2)]
      right
      linarith
  · -- Assume x = 9 ∨ x = (9 - Real.sqrt 17) / 2, prove x ≥ 0 ∧ 11 * x - x ^ 2 = 24 - 2 * Real.sqrt x
    rintro (h_eq | h_eq)
    · -- x = 9
      rw [h_eq]
      constructor
      · norm_num
      · -- Check the equation
        have h1 : Real.sqrt (9 : ℝ) = 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h1]
        all_goals norm_num
    · -- x = (9 - Real.sqrt 17) / 2
      rw [h_eq]
      constructor
      · -- Show x ≥ 0
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), sq_nonneg (Real.sqrt 17 - 4)]
      · -- Show 11 * x - x ^ 2 = 24 - 2 * Real.sqrt x
        have h10 : Real.sqrt ((9 - Real.sqrt 17) / 2) = (-1 + Real.sqrt 17) / 2 := by
          have h11 : 0 ≤ (9 - Real.sqrt 17 : ℝ) / 2 := by
            nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), sq_nonneg (Real.sqrt 17 - 4)]
          have h12 : Real.sqrt ((9 - Real.sqrt 17 : ℝ) / 2) = (-1 + Real.sqrt 17) / 2 := by
            have h13 : ((-1 + Real.sqrt 17) / 2) ^ 2 = (9 - Real.sqrt 17) / 2 := by
              nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), sq_nonneg (Real.sqrt 17 ^ 2 - 17)]
            have h14 : (-1 + Real.sqrt 17) / 2 ≥ 0 := by
              nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), sq_nonneg (Real.sqrt 17 ^ 2 - 17)]
            rw [← h13]
            field_simp [Real.sqrt_sq (show 0 ≤ (-1 + Real.sqrt 17) / 2 by linarith)]
          exact h12
        rw [h10]
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), sq_nonneg (Real.sqrt 17 ^ 2 - 17)]