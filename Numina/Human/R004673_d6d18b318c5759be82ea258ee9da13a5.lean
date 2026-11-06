import Mathlib
/-Given x/m+y/n+z/p = 1
m/x+n/y+p/z =0
calculate the value of x ^ 2 / m ^ 2 + y ^ 2 / n ^ 2 + z ^ 2 / p ^ 2-/
theorem algebra_297235 {x y z m n p : ℝ} (h1 : x ≠ 0) (h2 : y ≠ 0) (h3 : z ≠ 0)
    (h4 : m ≠ 0) (h5 : n ≠ 0) (h6 : p ≠ 0) (h7 : x / m + y / n + z / p = 1) (h8 : m / x + n / y + p / z = 0) :
    x ^ 2 / m ^ 2 + y ^ 2 / n ^ 2 + z ^ 2 / p ^ 2 = 1 := by
  have eq1 : x / m + y / n + z / p = 1 := h7
  have eq2 : m / x + n / y + p / z = 0 := h8
  --derive the first equation 
  have eq3 : m * y * z + n * x * z + p * x * y = 0 := by
    have h9 : m / x + n / y + p / z = 0 := h8
    field_simp [h1, h2, h3] at h9
    nlinarith
  -- derive the second equation
  have eq4 : (x * y) / (m * n) + (x * z) / (m * p) + (y * z) / (n * p) = 0 := by
    have h_eq3 : m * y * z + n * x * z + p * x * y = 0 := eq3
    have h9 : (x * y) / (m * n) + (x * z) / (m * p) + (y * z) / (n * p) = 0 := by
      have h13 : (x * y) / (m * n) + (x * z) / (m * p) + (y * z) / (n * p) = (p * x * y + n * x * z + m * y * z) / (m * n * p) := by
        have h14 : (x * y) / (m * n) = (x * y * p) / (m * n * p) := by
          field_simp [h4, h5, h6]
          ring
        have h15 : (x * z) / (m * p) = (x * z * n) / (m * n * p) := by
          field_simp [h4, h5, h6]
          ring
        have h16 : (y * z) / (n * p) = (y * z * m) / (m * n * p) := by
          field_simp [h4, h5, h6]
          ring
        rw [h14, h15, h16]
        ring
      have h17 : (p * x * y + n * x * z + m * y * z) = 0 := by
        linarith [h_eq3]
      have h18 : (p * x * y + n * x * z + m * y * z) / (m * n * p) = 0 := by
        rw [h17]
        norm_num
      linarith
    linarith
  
 -- final equation
  have h_eq1 : (x / m + y / n + z / p) ^ 2 = 1 := by
      rw [eq1]
      norm_num
  have h11 : (x / m + y / n + z / p) ^ 2 = (x ^ 2 / m ^ 2 + y ^ 2 / n ^ 2 + z ^ 2 / p ^ 2) + 2 * ((x * y) / (m * n) + (x * z) / (m * p) + (y * z) / (n * p)) := by
      field_simp [h4, h5, h6, h1, h2, h3]
      ring
  rw [h11] at h_eq1
  have h13 : (x * y) / (m * n) + (x * z) / (m * p) + (y * z) / (n * p) = 0 := by
      linarith [eq4]
  nlinarith
