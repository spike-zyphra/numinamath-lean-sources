import Mathlib

theorem algebra_311260 (x : ℤ) (hx : x ≥ 2009) (y : ℤ)
    (h : y = Real.sqrt (x + 2003) - Real.sqrt (x - 2009)) :
    y ≥ 2 := by
  have h1 : (x : ℝ) ≥ (2009 : ℝ) := by exact_mod_cast (show x ≥ (2009 : ℤ) by linarith)
  by_contra h9
  push_neg at h9
  have h10 : y ≤ 1 := by omega
  have h20 : (y : ℝ) > 0 := by
    have h21 : Real.sqrt (x + 2003) > Real.sqrt (x - 2009) := by
      have h22 : (x + 2003 : ℝ) > (x - 2009 : ℝ) := by
        nlinarith
      apply Real.sqrt_lt_sqrt
      · -- Show 0 ≤ (x - 2009 : ℝ)
        nlinarith
      · -- Show (x - 2009 : ℝ) < (x + 2003 : ℝ)
        nlinarith
    have h23 : Real.sqrt (x + 2003) - Real.sqrt (x - 2009) > 0 := by linarith
    have h24 : (y : ℝ) = Real.sqrt (x + 2003) - Real.sqrt (x - 2009) := by
      exact_mod_cast h
    nlinarith
  have h25 : y > 0 := by
    by_contra h26
    push_neg at h26
    have h27 : y ≤ 0 := by omega
    have h28 : (y : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h27
    nlinarith
  have h29 : y = 1 := by omega
  have h40 : (y : ℝ) = (1 : ℝ) := by exact_mod_cast h29
  have h41 : Real.sqrt (x + 2003) - Real.sqrt (x - 2009) = (1 : ℝ) := by
    have h44 : (y : ℝ) = Real.sqrt (x + 2003) - Real.sqrt (x - 2009) := by
      exact_mod_cast h
    linarith [h40, h44]
  have h42 : Real.sqrt (x + 2003) = Real.sqrt (x - 2009) + (1 : ℝ) := by linarith [h41]
  have h43 : Real.sqrt (x + 2003) ^ 2 = (Real.sqrt (x - 2009) + (1 : ℝ)) ^ 2 := by
    rw [h42]
  have h44 : Real.sqrt (x + 2003) ^ 2 = (x + 2003 : ℝ) := by
    have h45 : (x + 2003 : ℝ) ≥ 0 := by
      nlinarith
    rw [Real.sq_sqrt]
    linarith
  have h46 : (Real.sqrt (x - 2009) + (1 : ℝ)) ^ 2 = Real.sqrt (x - 2009) ^ 2 + 2 * Real.sqrt (x - 2009) + 1 := by
    ring
  have h47 : Real.sqrt (x - 2009) ^ 2 = (x - 2009 : ℝ) := by
    have h48 : (x - 2009 : ℝ) ≥ 0 := by
      nlinarith
    rw [Real.sq_sqrt]
    linarith
  rw [h46, h47] at h43
  rw [h44] at h43
  have h48 : Real.sqrt (x - 2009) = (2005.5 : ℝ) := by
    nlinarith
  have h49 : (x - 2009 : ℝ) = (2005.5 : ℝ) ^ 2 := by
    calc
      (x - 2009 : ℝ) = Real.sqrt (x - 2009) ^ 2 := by
        have h48' : (x - 2009 : ℝ) ≥ 0 := by
          nlinarith
        rw [Real.sq_sqrt]
        linarith
      _ = (2005.5 : ℝ) ^ 2 := by
        rw [h48]
  have h52 : 4 * (x - 2009 : ℤ) = (4011 : ℤ) ^ 2 := by
    have h53 : (4 * (x - 2009) : ℝ) = (4011 ^ 2 : ℝ) := by
      nlinarith
    have h54 : (4 * (x - 2009) : ℝ) = (4 * (x - 2009) : ℤ) := by
      simp
    rw [h54] at h53
    exact_mod_cast h53
  omega