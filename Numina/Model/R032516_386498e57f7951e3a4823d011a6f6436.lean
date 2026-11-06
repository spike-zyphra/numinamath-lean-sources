import Mathlib

theorem algebra_145460 (x y : ℝ) (h : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) ≥ 1) :
    x + y ≥ 0 := by 
  have h1 : x + Real.sqrt (x ^ 2 + 1) ≥ 0 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by positivity), sq_nonneg (x - Real.sqrt (x ^ 2 + 1)), sq_nonneg (x + Real.sqrt (x ^ 2 + 1)), sq_nonneg (x), sq_nonneg (Real.sqrt (x ^ 2 + 1) - x)]
  have h2 : y + Real.sqrt (y ^ 2 + 1) ≥ 0 := by
    nlinarith [Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (y ^ 2 + 1 : ℝ) by positivity), sq_nonneg (y - Real.sqrt (y ^ 2 + 1)), sq_nonneg (y + Real.sqrt (y ^ 2 + 1)), sq_nonneg (y), sq_nonneg (Real.sqrt (y ^ 2 + 1) - y)]
  set u := x + Real.sqrt (x^2 + 1)
  set v := y + Real.sqrt (y^2 + 1)
  have h3 : u * v ≥ 1 := h 
  have h4 : x = (u ^ 2 - 1) / (2 * u) := by
    have eq1 : u = x + Real.sqrt (x ^ 2 + 1) := by rfl
    have eq2 : Real.sqrt (x ^ 2 + 1) = u - x := by linarith 
    have eq3 : (Real.sqrt (x ^ 2 + 1)) ^ 2 = x ^ 2 + 1 := by 
      rw [Real.sq_sqrt]
      positivity 
    rw [eq2] at eq3 
    have h6 : (u - x) ^ 2 = x ^ 2 + 1 := eq3
    have h7 : u ^ 2 - 2 * u * x = 1 := by 
      nlinarith 
    have h8 : u ≠ 0 := by 
      by_contra h 
      rw [h] at h7 
      nlinarith 
    field_simp [h8]
    nlinarith 
  have h5 : y = (v ^ 2 - 1) / (2 * v) := by
    have eq1 : v = y + Real.sqrt (y ^ 2 + 1) := by rfl
    have eq2 : Real.sqrt (y ^ 2 + 1) = v - y := by linarith 
    have eq3 : (Real.sqrt (y ^ 2 + 1)) ^ 2 = y ^ 2 + 1 := by 
      rw [Real.sq_sqrt]
      positivity 
    rw [eq2] at eq3 
    have h6 : (v - y) ^ 2 = y ^ 2 + 1 := eq3
    have h7 : v ^ 2 - 2 * v * y = 1 := by 
      nlinarith 
    have h8 : v ≠ 0 := by 
      by_contra h 
      rw [h] at h7 
      nlinarith 
    field_simp [h8]
    nlinarith 
  have h6 : x + y = ((u * v - 1) * (u + v)) / (2 * (u * v)) := by
    rw [h4, h5]
    have h8 : u ≠ 0 := by
      by_contra h
      rw [h] at h3
      nlinarith
    have h9 : v ≠ 0 := by
      by_contra h
      rw [h] at h3
      nlinarith
    field_simp [h8, h9]
    nlinarith 
  have h8 : u * v - 1 ≥ 0 := by nlinarith 
  have h9 : u + v ≥ 0 := by nlinarith [h1, h2]
  have h10 : ((u * v - 1) * (u + v)) / (2 * (u * v)) ≥ 0 := by 
    apply div_nonneg 
    · -- Show the numerator is non-negative 
      nlinarith [h8, h9]
    · -- Show the denominator is non-negative 
      nlinarith [h3]
  linarith [h6, h10]