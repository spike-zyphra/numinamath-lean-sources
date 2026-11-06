import Mathlib

open Real

theorem algebra_15869 : IsGreatest {a : ℝ | ∃ x y z : ℝ, (x + y + z = 5) ∧ (x ≥ 0) ∧ (y ≥ 0) ∧ (z ≥ 0) ∧ a = sqrt (2 * x + 1) + sqrt (2 * y + 1) + sqrt (2 * z + 1)} (sqrt 39) := by
  constructor
  · -- Show that sqrt 39 is in the set.
    use 5 / 3, 5 / 3, 5 / 3
    constructor
    · -- Show 5/3 + 5/3 + 5/3 = 5
      norm_num
    constructor
    · -- Show x ≥ 0
      norm_num
    constructor
    · -- Show y ≥ 0
      norm_num
    constructor
    · -- Show z ≥ 0
      norm_num
    · -- Show the equality
      have h2 : sqrt (2 * (5 / 3 : ℝ) + 1) = Real.sqrt (13 / 3) := by
        rw [show (2 * (5 / 3 : ℝ) + 1) = (13 / 3 : ℝ) by norm_num]
      have h4 : 3 * Real.sqrt (13 / 3 : ℝ) = Real.sqrt 39 := by
        have h5 : (3 * Real.sqrt (13 / 3 : ℝ)) ^ 2 = (39 : ℝ) := by
          calc
            (3 * Real.sqrt (13 / 3 : ℝ)) ^ 2 = (3 : ℝ) ^ 2 * (Real.sqrt (13 / 3 : ℝ) ^ 2) := by ring
            _ = 9 * (13 / 3) := by
              have h6 : Real.sqrt (13 / 3 : ℝ) ^ 2 = (13 / 3 : ℝ) := by
                exact Real.sq_sqrt (by norm_num)
              rw [h6]
              all_goals norm_num
            _ = 39 := by norm_num
        have h6 : (Real.sqrt 39) ^ 2 = (39 : ℝ) := Real.sq_sqrt (by norm_num)
        have h7 : Real.sqrt 39 ≥ 0 := Real.sqrt_nonneg 39
        have h8 : 3 * Real.sqrt (13 / 3 : ℝ) ≥ 0 := by positivity
        nlinarith [h6, Real.sqrt_nonneg 39]
      rw [h2]
      linarith [h4]
  · -- Show that sqrt 39 is the greatest
    intro a ha
    rcases ha with ⟨x, y, z, h1, hx, hy, hz, heq⟩
    have h2 : sqrt (2 * x + 1) + sqrt (2 * y + 1) + sqrt (2 * z + 1) ≤ Real.sqrt 39 := by
      have h5 : (sqrt (2 * x + 1) + sqrt (2 * y + 1) + sqrt (2 * z + 1)) ^ 2 ≤ (39 : ℝ) := by
        nlinarith [sq_nonneg (sqrt (2 * x + 1) - sqrt (2 * y + 1)), sq_nonneg (sqrt (2 * y + 1) - sqrt (2 * z + 1)), sq_nonneg (sqrt (2 * z + 1) - sqrt (2 * x + 1)),
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x + 1 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * y + 1 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * z + 1 by linarith),
          mul_nonneg (Real.sqrt_nonneg (2 * x + 1)) (Real.sqrt_nonneg (2 * y + 1)), mul_nonneg (Real.sqrt_nonneg (2 * y + 1)) (Real.sqrt_nonneg (2 * z + 1)), mul_nonneg (Real.sqrt_nonneg (2 * z + 1)) (Real.sqrt_nonneg (2 * x + 1)),
          h1, sq_nonneg (x - 5 / 3), sq_nonneg (y - 5 / 3), sq_nonneg (z - 5 / 3),
          mul_nonneg (show (0 : ℝ) ≤ (x) by linarith) (show (0 : ℝ) ≤ (y) by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ (y) by linarith) (show (0 : ℝ) ≤ (z) by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ (z) by linarith) (show (0 : ℝ) ≤ (x) by linarith)
        ]
      have h6 : (Real.sqrt 39) ^ 2 = (39 : ℝ) := Real.sq_sqrt (by norm_num)
      have h7 : Real.sqrt 39 ≥ 0 := Real.sqrt_nonneg 39
      have h8 : sqrt (2 * x + 1) + sqrt (2 * y + 1) + sqrt (2 * z + 1) ≥ 0 := by positivity
      nlinarith [h5, Real.sqrt_nonneg 39, Real.sq_sqrt (show (0 : ℝ) ≤ (39 : ℝ) by norm_num)]
    nlinarith [h2, Real.sq_sqrt (show (0 : ℝ) ≤ (39 : ℝ) by norm_num), heq]