import Mathlib

theorem algebra_216721 (x y z : ℝ) (hx : x - 4 ≥ 0) (hy : y - 9 ≥ 0) (hz : z - 16 ≥ 0)
    (h : 2 * Real.sqrt (x - 4) + 3 * Real.sqrt (y - 9) + 4 * Real.sqrt (z - 16) =
    (x + y + z) / 2) :
    x = 8 ∧ y = 18 ∧ z = 32 := by

  have ha1 : (Real.sqrt (x - 4)) ^ 2 = x - 4 := by
    rw [Real.sq_sqrt]
    linarith

  have hb1 : (Real.sqrt (y - 9)) ^ 2 = y - 9 := by
    rw [Real.sq_sqrt]
    linarith

  have hc1 : (Real.sqrt (z - 16)) ^ 2 = z - 16 := by
    rw [Real.sq_sqrt]
    linarith

  have eq4 : (Real.sqrt (x - 4) - 2) ^ 2 + (Real.sqrt (y - 9) - 3) ^ 2 + (Real.sqrt (z - 16) - 4) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (x - 4) - 2), sq_nonneg (Real.sqrt (y - 9) - 3), sq_nonneg (Real.sqrt (z - 16) - 4),
      Real.sqrt_nonneg (x - 4), Real.sqrt_nonneg (y - 9), Real.sqrt_nonneg (z - 16)]
  
  have ha2' : Real.sqrt (x - 4) - 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (x - 4) - 2), sq_nonneg (Real.sqrt (y - 9) - 3), sq_nonneg (Real.sqrt (z - 16) - 4), eq4]

  have hb2' : Real.sqrt (y - 9) - 3 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (x - 4) - 2), sq_nonneg (Real.sqrt (y - 9) - 3), sq_nonneg (Real.sqrt (z - 16) - 4), eq4]

  have hc2' : Real.sqrt (z - 16) - 4 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (x - 4) - 2), sq_nonneg (Real.sqrt (y - 9) - 3), sq_nonneg (Real.sqrt (z - 16) - 4), eq4]

  have h10 : x = 8 := by
    have hx2 : x - 4 = 4 := by
      calc
        x - 4 = (Real.sqrt (x - 4)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (2 : ℝ) ^ 2 := by
          have h1 : Real.sqrt (x - 4) = 2 := by linarith [ha2']
          rw [h1]
        _ = (4 : ℝ) := by
          norm_num
    linarith [hx2]

  have h11 : y = 18 := by
    have hy2 : y - 9 = 9 := by
      calc
        y - 9 = (Real.sqrt (y - 9)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (3 : ℝ) ^ 2 := by
          have h1 : Real.sqrt (y - 9) = 3 := by linarith [hb2']
          rw [h1]
        _ = (9 : ℝ) := by
          norm_num
    linarith [hy2]

  have h12 : z = 32 := by
    have hz2 : z - 16 = 16 := by
      calc
        z - 16 = (Real.sqrt (z - 16)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (4 : ℝ) ^ 2 := by
          have h1 : Real.sqrt (z - 16) = 4 := by linarith [hc2']
          rw [h1]
        _ = (16 : ℝ) := by
          norm_num
    linarith [hz2]

  exact ⟨h10, h11, h12⟩