import Mathlib

theorem algebra_609101 :
    IsLeast {α : ℝ | ∃ x y z : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ z ≤ 4 ∧ y ^ 2 = x ^ 2 + 2 ∧ z ^ 2 = y ^ 2 + 2 ∧ α = |x - y| + |y - z|} (4 - 2 * Real.sqrt 3) := by
  constructor
  · -- Show that 4 - 2 * Real.sqrt 3 is achievable.
    use 2 * Real.sqrt 3, Real.sqrt 14, 4
    constructor
    · -- Show 0 ≤ 2 * Real.sqrt 3
      positivity
    constructor
    · -- Show 2 * Real.sqrt 3 ≤ Real.sqrt 14
      have h1 : (2 * Real.sqrt 3) ^ 2 ≤ (Real.sqrt 14) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 14, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (14 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3), sq_nonneg (Real.sqrt 14)]
      have h2 : 2 * Real.sqrt 3 ≤ Real.sqrt 14 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 14, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (14 : ℝ) by norm_num)]
      exact h2
    constructor
    · -- Show Real.sqrt 14 ≤ 4
      have h1 : Real.sqrt 14 ≤ 4 := by
        rw [Real.sqrt_le_iff] <;> norm_num
      exact h1
    constructor
    · -- Show 4 ≤ 4
      norm_num
    constructor
    · -- Show (Real.sqrt 14) ^ 2 = (2 * Real.sqrt 3) ^ 2 + 2
      have h1 : (Real.sqrt 14) ^ 2 = 14 := Real.sq_sqrt (by norm_num)
      have h2 : (2 * Real.sqrt 3) ^ 2 = 12 := by
        calc
          (2 * Real.sqrt 3) ^ 2 = 4 * (Real.sqrt 3) ^ 2 := by ring
          _ = 4 * 3 := by rw [Real.sq_sqrt]; positivity
          _ = 12 := by norm_num
      linarith
    constructor
    · -- Show (4 : ℝ) ^ 2 = (Real.sqrt 14) ^ 2 + 2
      have h1 : (Real.sqrt 14) ^ 2 = 14 := Real.sq_sqrt (by norm_num)
      nlinarith
    · -- Show 4 - 2 * Real.sqrt 3 = |2 * Real.sqrt 3 - Real.sqrt 14| + |Real.sqrt 14 - 4|
      have h3 : Real.sqrt 14 ≤ 4 := by
        rw [Real.sqrt_le_iff] <;> norm_num
      have h4 : 2 * Real.sqrt 3 ≤ Real.sqrt 14 := by
        have h1 : (2 * Real.sqrt 3) ^ 2 ≤ (Real.sqrt 14) ^ 2 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 14, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (14 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3), sq_nonneg (Real.sqrt 14)]
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 14]
      rw [abs_of_nonpos (by linarith [h4]), abs_of_nonpos (by linarith [h3, Real.sqrt_nonneg 14, show (4 : ℝ) ≥ Real.sqrt 14 by linarith [h3] ])]
      nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (14 : ℝ) by norm_num)]
  · -- Show that 4 - 2 * Real.sqrt 3 is the least element in the set.
    intro α hα
    rcases hα with ⟨x, y, z, hx0, hxy, hyz, hz4, h1, h2, h_eq⟩
    have h3 : α = z - x := by
      rw [h_eq]
      have h4 : x ≤ y := hxy
      have h5 : y ≤ z := hyz
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      all_goals linarith
    rw [h3]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (z - 4), sq_nonneg (x ^ 2 - 12), sq_nonneg (y ^ 2 - 14), sq_nonneg (z ^ 2 - 16), sq_nonneg ((x - (2 * Real.sqrt 3))), Real.sq_sqrt (show 0 ≤ (14 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (16 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 14, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]