import Mathlib

theorem algebra_248990 : Real.sqrt (7 - Real.sqrt 48) + Real.sqrt (5 - Real.sqrt 24) + Real.sqrt (3 - Real.sqrt 8) = 1 := by

  have h1 : Real.sqrt 48 = 4 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
    all_goals norm_num

  have h2 : Real.sqrt 24 = 2 * Real.sqrt 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h3 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h4 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num


  have h9 : Real.sqrt (7 - Real.sqrt 48) = 2 - Real.sqrt 3 := by
    rw [h1]
    have h10 : 7 - (4 * Real.sqrt 3) = (Real.sqrt 3 - 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [h10]
    have h12 : Real.sqrt ((Real.sqrt 3 - 2) ^ 2) = |Real.sqrt 3 - 2| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h12]
    have h13 : Real.sqrt 3 < (2 : ℝ) := by
      have h14 : Real.sqrt 3 < (2 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
        all_goals nlinarith
      linarith
    rw [abs_of_neg (by linarith [h13, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)])]
    <;> try ring_nf
    <;> try linarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]

  have h10 : Real.sqrt (5 - Real.sqrt 24) = Real.sqrt 3 - Real.sqrt 2 := by
    rw [h2]
    rw [h4]
    have h11 : 5 - (2 * (Real.sqrt 2 * Real.sqrt 3)) = (Real.sqrt 3 - Real.sqrt 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - Real.sqrt 2)]
    rw [h11]
    have h15 : Real.sqrt ((Real.sqrt 3 - Real.sqrt 2) ^ 2) = |Real.sqrt 3 - Real.sqrt 2| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h15]
    have h13 : Real.sqrt 3 > Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
      all_goals nlinarith
    have h16 : Real.sqrt 3 - Real.sqrt 2 > 0 := by linarith [h13]
    rw [abs_of_pos h16]
    <;> try ring_nf
    <;> try linarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]

  have h9' : Real.sqrt (3 - Real.sqrt 8) = Real.sqrt 2 - 1 := by
    rw [h3]
    have h12 : 3 - (2 * Real.sqrt 2) = (Real.sqrt 2 - 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    rw [h12]
    have h13 : Real.sqrt ((Real.sqrt 2 - 1) ^ 2) = |Real.sqrt 2 - 1| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h13]
    have h14 : Real.sqrt 2 - 1 > (0 : ℝ) := by
      have h15 : Real.sqrt 2 > 1 := by
        have : Real.sqrt 2 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        have h16 : Real.sqrt 1 = 1 := Real.sqrt_one
        linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), h16]
      linarith
    rw [abs_of_pos h14]
    <;> try ring_nf
    <;> try linarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]

  rw [h9, h10, h9']
  <;> ring_nf <;> norm_num
  all_goals linarith
  all_goals ring_nf <;> norm_num
  all_goals try linarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]