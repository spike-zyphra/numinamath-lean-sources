import Mathlib

theorem algebra_9246 {x y : ℝ} (h : (x + y) / (1 - x * y) = Real.sqrt 5) :
    abs (1 - x * y) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) = Real.sqrt 6 / 6 := by

  have h1 : (1 - x * y) ≠ 0 := by 
    by_contra h2
    have eq1 : (x + y) / (1 - x * y) = 0 := by 
      rw [h2]
      norm_num
    have eq2 : Real.sqrt 5 = 0 := by linarith [h, eq1]
    have eq3 : Real.sqrt 5 > 0 := by
      positivity
    linarith [eq2, eq3]

  have h2 : ((x + y) / (1 - x * y)) ^ 2 = 5 := by 
    calc 
      ((x + y) / (1 - x * y)) ^ 2 = (Real.sqrt 5) ^ 2 := by rw [h]
      _ = 5 := by 
        norm_num [Real.sq_sqrt]

  have h3 : (x + y) ^ 2 = 5 * (1 - x * y) ^ 2 := by 
    have h4 : ((x + y) / (1 - x * y)) ^ 2 = 5 := h2
    field_simp [h1] at h4 ⊢
    nlinarith

  have h4 : ((1 - x * y) ^ 2) / ((1 + x ^ 2) * (1 + y ^ 2)) = 1 / 6 := by
    have eq1 : (x + y) ^ 2 = 5 * (1 - x * y) ^ 2 := h3
    have eq2 : (1 + x ^ 2) * (1 + y ^ 2) = 6 * ((1 - x * y) ^ 2) := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x + y - 2 * (x * y)), sq_nonneg ((x * y) * (x * y) - 1)]
    have eq3 : (1 - x * y) ^ 2 / ((1 + x ^ 2) * (1 + y ^ 2)) = 1 / 6 := by 
      rw [eq2]
      field_simp
      <;> nlinarith
    exact_mod_cast eq3

  have h5 : (abs (1 - x * y) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2))) ^ 2 = 1 / 6 := by
    have h6 : (abs (1 - x * y) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2))) ^ 2 = (abs (1 - x * y) ^ 2) / ((Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) ^ 2) := by 
      field_simp
    rw [h6]
    have h7 : (abs (1 - x * y) ^ 2) = (1 - x * y) ^ 2 := by 
      simp [abs_pow]
    have h8 : (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) ^ 2 = (1 + x ^ 2) * (1 + y ^ 2) := by 
      calc 
        (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) ^ 2 = (Real.sqrt (1 + x ^ 2)) ^ 2 * (Real.sqrt (1 + y ^ 2)) ^ 2 := by 
          ring
        _ = (1 + x ^ 2) * (1 + y ^ 2) := by 
          rw [Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)]
    rw [h7, h8]
    linarith [h4]

  have h6 : abs (1 - x * y) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) ≥ 0 := by
    apply div_nonneg
    · -- Show abs (1 - x * y) ≥ 0
      positivity
    · -- Show Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) ≥ 0
      positivity

  have h7 : abs (1 - x * y) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) = Real.sqrt (1 / 6) := by
    have h8 : (abs (1 - x * y) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2))) ^ 2 = 1 / 6 := h5
    have h9 : 0 ≤ abs (1 - x * y) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) := h6
    have h10 : Real.sqrt ((abs (1 - x * y) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2))) ^ 2) = Real.sqrt (1 / 6) := by 
      rw [h8]
    have h11 : Real.sqrt ((abs (1 - x * y) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2))) ^ 2) = abs (1 - x * y) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) := by 
      rw [Real.sqrt_sq (by linarith)]
    nlinarith [h10, h11]

  rw [h7]
  have h8 : Real.sqrt (1 / 6) = Real.sqrt 6 / 6 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h8]