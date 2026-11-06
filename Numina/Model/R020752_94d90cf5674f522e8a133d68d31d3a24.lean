import Mathlib

open Real

theorem algebra_14688 {x : ℝ} (hx : 2 < x ∧ x ≠ 3 / 5) :
    logb 2 ((3 * x + 9) / (5 * x - 3)) + logb 2 ((5 * x - 3) / (x - 2)) = 2 ↔ x = 17 := by
  constructor
  · -- Assume the equation holds, we need to prove x = 17
    intro h_eq
    have h1 : 0 < (3 * x + 9) / (5 * x - 3) := by
      have hx1 : 5 * x - 3 > 0 := by
        have h2x : x > 2 := hx.1
        linarith
      have hx2 : 3 * x + 9 > 0 := by
        have h2x : x > 2 := hx.1
        linarith
      positivity
    have h2 : 0 < (5 * x - 3) / (x - 2) := by
      have hx3 : x - 2 > 0 := by
        linarith [hx.1]
      have hx4 : 5 * x - 3 > 0 := by
        have h2x : x > 2 := hx.1
        linarith
      positivity
    have h3 : logb 2 ((3 * x + 9) / (5 * x - 3)) + logb 2 ((5 * x - 3) / (x - 2)) =
        logb 2 (((3 * x + 9) / (5 * x - 3)) * ((5 * x - 3) / (x - 2))) := by
      rw [← logb_mul (by positivity) (by positivity)]
    have h4 : ((3 * x + 9) / (5 * x - 3)) * ((5 * x - 3) / (x - 2)) = (3 * (x + 3) / (x - 2)) := by
      field_simp [(show 5 * x - 3 ≠ 0 by
          intro h
          have h5 : x = 3 / 5 := by linarith
          tauto
        ), (show x - 2 ≠ 0 by
          linarith [hx.1]
        )
      ]
      ring
    rw [h3] at h_eq
    rw [h4] at h_eq
    have h5 : (3 * (x + 3) / (x - 2) : ℝ) = 4 := by 
      have h6 : (3 * (x + 3) / (x - 2) : ℝ) > 0 := by
        have hx3 : x - 2 > 0 := by
          linarith [hx.1]
        have hx4 : 3 * (x + 3) > 0 := by
          have h2x : x > 2 := hx.1
          linarith
        positivity
      rw [logb_eq_iff_rpow_eq] at h_eq
      · -- Prove x^pow = value
        norm_num at h_eq ⊢
        all_goals
          try linarith
          try tauto
      all_goals
        try linarith
        try tauto
    have h6 : 3 * (x + 3) = 4 * (x - 2) := by
      have hx3 : x - 2 > 0 := by
        linarith [hx.1]
      have h7 : x - 2 > 0 := by
        linarith [hx.1]
      field_simp at h5
      nlinarith
    linarith
  · -- Assume x = 17, prove the equation
    intro h_eq
    rw [h_eq]
    have h11 : (3 * (17 : ℝ) + 9) / (5 * (17 : ℝ) - 3) = (30 / 41 : ℝ) := by norm_num
    have h12 : (5 * (17 : ℝ) - 3) / (17 - 2) = (82 / 15 : ℝ) := by norm_num
    have h13 : logb 2 ((3 * (17 : ℝ) + 9) / (5 * (17 : ℝ) - 3)) + logb 2 ((5 * (17 : ℝ) - 3) / (17 - 2)) =
        logb 2 ((3 * (17 : ℝ) + 9) / (5 * (17 : ℝ) - 3) * ((5 * (17 : ℝ) - 3) / (17 - 2))) := by
      rw [← logb_mul (by positivity) (by positivity)]
    have h14 : ((3 * (17 : ℝ) + 9) / (5 * (17 : ℝ) - 3) * ((5 * (17 : ℝ) - 3) / (17 - 2)) ) = (4 : ℝ) := by
      rw [h11, h12]
      norm_num
    rw [h13]
    rw [h14]
    have h15 : logb (2 : ℝ) (4 : ℝ) = 2 := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    rw [h15]