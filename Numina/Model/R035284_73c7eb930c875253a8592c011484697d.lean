import Mathlib

theorem algebra_263651 {x : ℝ} (hx : x > 0) (h : 2 * Real.sqrt x + 2 * x ^ (-1 / 2 : ℝ) = 5) :
    4 * x ^ 2 - 17 * x + 4 = 0 := by

  have h1 : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by 
    have h2 : x ^ (-1 / 2 : ℝ) = (x ^ (1 / 2 : ℝ)) ^ (-1 : ℝ) := by 
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h2]
    have h3 : (x ^ (1 / 2 : ℝ)) ^ (-1 : ℝ) = 1 / (x ^ (1 / 2 : ℝ)) := by 
      simp [Real.rpow_neg_one]
    rw [h3]
    have h4 : x ^ (1 / 2 : ℝ) = Real.sqrt x := by 
      rw [Real.sqrt_eq_rpow]
    rw [h4]
  rw [h1] at h
  have h2 : Real.sqrt x > 0 := by 
    apply Real.sqrt_pos.mpr
    linarith
  have eq1 : 2 * x + 2 = 5 * Real.sqrt x := by
    have h4 : (2 * Real.sqrt x + 2 * (1 / Real.sqrt x)) * Real.sqrt x = 2 * x + 2 := by 
      have h2' : Real.sqrt x > 0 := h2
      field_simp [h2']
      <;> nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith)]
    have h5 : (2 * Real.sqrt x + 2 * (1 / Real.sqrt x)) * Real.sqrt x = 5 * Real.sqrt x := by
      nlinarith [h, Real.sqrt_nonneg x]
    linarith [h4, h5]
  have h4 : (2 * x + 2) ^ 2 = 25 * x := by
    calc
      (2 * x + 2) ^ 2 = (5 * Real.sqrt x) ^ 2 := by 
        rw [eq1]
      _ = 25 * (Real.sqrt x) ^ 2 := by 
        ring_nf
      _ = 25 * x := by 
        rw [Real.sq_sqrt]
        nlinarith
  nlinarith