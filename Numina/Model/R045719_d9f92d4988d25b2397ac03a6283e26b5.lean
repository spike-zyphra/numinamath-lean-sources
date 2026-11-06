import Mathlib

theorem algebra_241873 (x y : ℝ) :
    (x ^ 4 + 9 * x ^ 2 + 4) * (y ^ 4 - 3 * y ^ 2 + 17) = 59 ↔
    (x = 0 ∧ y = Real.sqrt (3 / 2)) ∨ (x = 0 ∧ y = -Real.sqrt (3 / 2)) := by 
  constructor
  · -- Assume the equation holds, prove the possible solutions
    intro h
    have h1 : x ^ 4 + 9 * x ^ 2 + 4 ≥ 4 := by 
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 3 / 2)]
    have h2 : y ^ 4 - 3 * y ^ 2 + 17 ≥ 59 / 4 := by
      nlinarith [sq_nonneg (y ^ 2 - 3 / 2), sq_nonneg (y), sq_nonneg (y - Real.sqrt (3 / 2)), sq_nonneg (y + Real.sqrt (3 / 2)), Real.sqrt_nonneg (3 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (3 / 2 : ℝ) by norm_num)]
    have h3 : x ^ 4 + 9 * x ^ 2 + 4 = 4 := by
      nlinarith [h, h1, h2, mul_nonneg (show 0 ≤ x ^ 4 + 9 * x ^ 2 + 4 by nlinarith) (show 0 ≤ y ^ 4 - 3 * y ^ 2 + 17 by nlinarith)]
    have hx : x = 0 := by
      have h4 : x ^ 4 + 9 * x ^ 2 = 0 := by
        nlinarith [h3]
      have h5 : x ^ 2 = 0 := by
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x)]
      have h6 : x = 0 := by 
        nlinarith
      exact h6
    have h4 : y ^ 4 - 3 * y ^ 2 + 17 = 59 / 4 := by 
      nlinarith [h, h1, h2, h3, mul_nonneg (show 0 ≤ x ^ 4 + 9 * x ^ 2 + 4 by nlinarith) (show 0 ≤ y ^ 4 - 3 * y ^ 2 + 17 by nlinarith)]
    have h5 : (y ^ 2 - 3 / 2) ^ 2 = 0 := by 
      nlinarith [h4]
    have hy1 : y ^ 2 = 3 / 2 := by
      nlinarith
    have hy2 : y = Real.sqrt (3 / 2) ∨ y = -Real.sqrt (3 / 2) := by
      have h6 : y^2 = (3/2: ℝ) := hy1
      have h7 : y^2 = (Real.sqrt (3/2: ℝ)) ^ 2 := by
        rw [h6]
        rw [Real.sq_sqrt]
        linarith
      have h8 : y = Real.sqrt (3/2: ℝ) ∨ y = -Real.sqrt (3/2: ℝ) := by
        apply eq_or_eq_neg_of_sq_eq_sq 
        all_goals 
          nlinarith [h7, Real.sqrt_nonneg (3/2: ℝ)]
      exact h8
    rcases hy2 with (h8 | h8)
    · -- Case y = Real.sqrt (3 / 2)
      left
      tauto
    · -- Case y = -Real.sqrt (3 / 2)
      right
      tauto
  · -- Backward direction: if the solutions are given, then the equation holds
    rintro (h | h)
    · -- Case (x = 0 ∧ y = Real.sqrt (3 / 2))
      rcases h with ⟨hx, hy⟩ 
      rw [hx, hy]
      have h3 : (Real.sqrt (3 / 2 : ℝ)) ^ 2 = (3 / 2 : ℝ) := by 
        rw [Real.sq_sqrt]
        norm_num
      have h4 : (Real.sqrt (3 / 2 : ℝ)) ^ 4 = (9 / 4 : ℝ) := by
        calc
          (Real.sqrt (3 / 2 : ℝ)) ^ 4
              = ((Real.sqrt (3 / 2 : ℝ)) ^ 2) ^ 2 := by ring
          _   = (3 / 2 : ℝ) ^ 2 := by rw [h3]
          _   = (9 / 4 : ℝ) := by norm_num
      nlinarith [h3, h4]
    · -- Case (x = 0 ∧ y = -Real.sqrt (3 / 2))
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      have h3 : (-Real.sqrt (3 / 2 : ℝ)) ^ 2 = (3 / 2 : ℝ) := by
        have h3 : (Real.sqrt (3 / 2 : ℝ)) ^ 2 = (3 / 2 : ℝ) := by 
          rw [Real.sq_sqrt]
          norm_num
        nlinarith [h3, sq_nonneg (Real.sqrt (3 / 2 : ℝ)), Real.sqrt_nonneg (3 / 2)]
      have h4 : (-Real.sqrt (3 / 2 : ℝ)) ^ 4 = (9 / 4 : ℝ) := by
        calc
          (-Real.sqrt (3 / 2 : ℝ)) ^ 4
              = ((-Real.sqrt (3 / 2 : ℝ)) ^ 2) ^ 2 := by ring
          _   = (3 / 2 : ℝ) ^ 2 := by rw [h3]
          _   = (9 / 4 : ℝ) := by norm_num
      nlinarith [h3, h4]