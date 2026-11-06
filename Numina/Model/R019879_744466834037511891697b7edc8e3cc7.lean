import Mathlib

theorem algebra_161101 (x : ℝ) (hx : x = (4 + Real.sqrt 80) ^ ((1 : ℝ) / 3) - (Real.sqrt 80 - 4) ^ ((1 : ℝ) / 3)) :
    x ^ 3 + 12 * x - 8 = 0 := by
  have h1 : Real.sqrt 80 = 4 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h2 : (4 + Real.sqrt 80 : ℝ) * (Real.sqrt 80 - 4) = 64 := by
    rw [h1]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h3 : ((4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3)) = (4 : ℝ) := by
    have h4 : ((4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3)) =
        ((4 + Real.sqrt 80 : ℝ) * (Real.sqrt 80 - 4 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals nlinarith [Real.sqrt_nonneg 80, Real.sqrt_nonneg 5, h1]
    rw [h4]
    have h5 : ((4 + Real.sqrt 80 : ℝ) * (Real.sqrt 80 - 4 : ℝ)) = (64 : ℝ) := h2
    rw [h5]
    have h6 : (64 : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
      have h7 : (64 : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
        rw [show (64 : ℝ) = 4 ^ (3 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      linarith
    linarith
  rw [hx]
  have h4 : ((4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (4 + Real.sqrt 80 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals nlinarith [Real.sqrt_nonneg 80, Real.sqrt_nonneg 5, h1]
  have h5 : ((Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (Real.sqrt 80 - 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals nlinarith [Real.sqrt_nonneg 80, Real.sqrt_nonneg 5, h1]
  have eq1 : ((4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 =
      ((4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 - ((Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 - 3 * (( (4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 * ((Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3)) ) + 3 * ( (4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) * ( (Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) := by
    ring
  have eq6 : -3 * (( (4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 * ((Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3)) ) + 3 * ( (4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) * ( (Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) = - 12 * ((4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3) ) := by
    have eq5 : ((4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) ) * ((Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3) ) = (4 : ℝ) := h3
    have eq7 : -3 * (( (4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 * ((Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3)) ) + 3 * ( (4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) * ( (Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) = 3 * (( (4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) ) * ((Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3) ) ) * ( ( (Real.sqrt 80 - 4 : ℝ) ^ ((1 : ℝ) / 3) ) - ( (4 + Real.sqrt 80 : ℝ) ^ ((1 : ℝ) / 3) ) ) := by 
      ring
    rw [eq7]
    rw [eq5]
    all_goals norm_num 
    <;> nlinarith
  rw [eq1]
  simp only [h4, h5]
  linarith [eq6]