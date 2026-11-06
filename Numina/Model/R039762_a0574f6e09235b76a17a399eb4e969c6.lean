import Mathlib

theorem algebra_10498 (x : ℝ) (hx : x ≥ 1) : Real.sqrt (5 * x) / Real.sqrt (3 * (x - 1)) = 2 ↔ x = 12 / 7 := by
  constructor
  · -- Assume $\frac{\sqrt{5x}}{\sqrt{3(x-1)}} = 2$, prove $x = \frac{12}{7}$
    intro h
    have h1 : x - 1 > 0 := by
      by_contra h2
      push_neg at h2
      have h3 : x ≤ 1 := by linarith
      have h4 : x = 1 := by linarith
      rw [show x = 1 by linarith] at h
      norm_num [Real.sqrt_eq_zero] at h
      all_goals linarith
    have h2 : Real.sqrt (3 * (x - 1)) > 0 := by
      apply Real.sqrt_pos.mpr
      nlinarith
    have h3 : Real.sqrt (5 * x) = 2 * Real.sqrt (3 * (x - 1)) := by
      field_simp [h2] at h ⊢
      linarith
    have h4 : Real.sqrt (5 * x) ^ 2 = (2 * Real.sqrt (3 * (x - 1))) ^ 2 := by
      rw [h3]
    have h5 : Real.sqrt (5 * x) ^ 2 = 5 * x := by
      apply Real.sq_sqrt
      nlinarith
    have h6 : (2 * Real.sqrt (3 * (x - 1))) ^ 2 = 4 * (3 * (x - 1)) := by
      calc
        (2 * Real.sqrt (3 * (x - 1))) ^ 2
          = 4 * (Real.sqrt (3 * (x - 1)) ^ 2) := by
            ring_nf
        _ = 4 * (3 * (x - 1)) := by
          rw [Real.sq_sqrt]
          all_goals
          nlinarith
    rw [h5] at h4
    rw [h6] at h4
    nlinarith
  · -- Assume x = 12/7, prove the equation
    intro h_eq
    rw [h_eq]
    have h8 : Real.sqrt (5 * (12 / 7 : ℝ)) / Real.sqrt (3 * (12 / 7 - 1 : ℝ)) = 2 := by
      have h2 : Real.sqrt (5 * (12 / 7 : ℝ)) / Real.sqrt (3 * (12 / 7 - 1 : ℝ)) = Real.sqrt ((5 * (12 / 7 : ℝ)) / (3 * (12 / 7 - 1 : ℝ))) := by
        field_simp [Real.sqrt_div]
      rw [h2]
      have h3 : ((5 * (12 / 7 : ℝ)) / (3 * (12 / 7 - 1 : ℝ))) = (4 : ℝ) := by
        norm_num
      rw [h3]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith