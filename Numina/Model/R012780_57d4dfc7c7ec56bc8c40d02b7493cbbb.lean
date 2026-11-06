import Mathlib

theorem algebra_253082 (x y z : ℝ) (h : 0 ≤ x - y + z) (h' : 0 ≤ x) (h'' : 0 ≤ y) (h''' : 0 ≤ z)
    (h'''' : Real.sqrt (x - y + z) = Real.sqrt x - Real.sqrt y + Real.sqrt z) :
    (x - y) * (y - z) * (z - x) = 0 := by

  have h1 : (Real.sqrt (x - y + z)) ^ 2 = (Real.sqrt x - Real.sqrt y + Real.sqrt z) ^ 2 := by 
    rw [h'''']
  have h2 : (Real.sqrt (x - y + z)) ^ 2 = x - y + z := Real.sq_sqrt (by linarith)
  have h3 : (Real.sqrt x - Real.sqrt y + Real.sqrt z) ^ 2 =
      (Real.sqrt x) ^ 2 + (Real.sqrt y) ^ 2 + (Real.sqrt z) ^ 2 + 2 * (Real.sqrt x * (-Real.sqrt y) + Real.sqrt x * Real.sqrt z + (-Real.sqrt y) * Real.sqrt z) := by ring
  rw [h2] at h1
  rw [h3] at h1
  have h4 : (Real.sqrt x) ^ 2 = x := by 
    apply Real.sq_sqrt 
    linarith
  have h5 : (Real.sqrt y) ^ 2 = y := by 
    apply Real.sq_sqrt
    linarith
  have h6 : (Real.sqrt z) ^ 2 = z := by 
    apply Real.sq_sqrt
    linarith
  rw [h4, h5, h6] at h1
  have eq1 : -2 * y = -2 * (Real.sqrt x * Real.sqrt y) + 2 * (Real.sqrt x * Real.sqrt z) - 2 * (Real.sqrt y * Real.sqrt z) := by
    nlinarith
  have eq2 : y = Real.sqrt x * Real.sqrt y - Real.sqrt x * Real.sqrt z + Real.sqrt y * Real.sqrt z := by
    nlinarith
  have h7 : (y - x) * (y - z) = 0 := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt y - Real.sqrt z), 
      sq_nonneg (Real.sqrt x - Real.sqrt z), Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z, 
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), 
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg z), 
      mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg z)]
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- Case $y - x = 0$
    have : x - y = 0 := by 
      linarith
    rw [this]
    norm_num
  · -- Case $y - z = 0$
    have : y - z = 0 := by 
      linarith
    rw [this]
    norm_num