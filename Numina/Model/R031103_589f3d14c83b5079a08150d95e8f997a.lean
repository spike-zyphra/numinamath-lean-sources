import Mathlib

theorem algebra_142905 (y : ℝ) (h : 2 * 3 - 3 * y + 15 = 0) (x : ℝ)
    (hx : Real.sqrt ((x - 3) ^ 2 + (4 - y) ^ 2) = 3 * Real.sqrt 5) :
    x = 9 ∨ x = -3 := by

  have hy : y = 7 := by
    linarith

  have eq1 : Real.sqrt ((x - 3) ^ 2 + (4 - y) ^ 2) = 3 * Real.sqrt 5 := hx

  rw [hy] at eq1

  have h1 : (x - 3) ^ 2 + (4 - (7 : ℝ)) ^ 2 = 45 := by
    have h2 : Real.sqrt ((x - 3) ^ 2 + (4 - (7 : ℝ)) ^ 2) = 3 * Real.sqrt 5 := eq1
    have h3 : Real.sqrt ((x - 3) ^ 2 + (4 - (7 : ℝ)) ^ 2) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h4 : (3 * Real.sqrt 5 : ℝ) ≥ 0 := by
      have h5 : Real.sqrt 5 ≥ 0 := by
        apply Real.sqrt_nonneg
      nlinarith
    have h6 : (Real.sqrt ((x - 3) ^ 2 + (4 - (7 : ℝ)) ^ 2)) ^ 2 = (3 * Real.sqrt 5) ^ 2 := by
      rw [h2]
    have h7 : (Real.sqrt ((x - 3) ^ 2 + (4 - (7 : ℝ)) ^ 2)) ^ 2 = (x - 3) ^ 2 + (4 - (7 : ℝ)) ^ 2 := by
      exact Real.sq_sqrt (by nlinarith)
    have h8 : (3 * Real.sqrt 5 : ℝ) ^ 2 = 45 := by
      calc
        (3 * Real.sqrt 5 : ℝ) ^ 2 = 9 * (Real.sqrt 5) ^ 2 := by ring
        _ = 9 * 5 := by
          rw [Real.sq_sqrt]
          all_goals linarith
        _ = 45 := by norm_num
    rw [h7] at h6
    rw [h8] at h6
    linarith

  have h8 : (x - 9) * (x + 3) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h8) with h9 h3
  · -- x - 9 = 0, so x = 9
    left
    linarith
  · -- x + 3 = 0, so x = -3
    right
    linarith