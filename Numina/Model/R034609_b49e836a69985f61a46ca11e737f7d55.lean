import Mathlib

theorem algebra_217340 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h : x + y + x * y = 1) :
    x * y + 1 / (x * y) - y / x - x / y = 4 := by

  have h1 : x + y = 1 - x * y := by linarith
  have h2 : (x + y) ^ 2 = (1 - x * y) ^ 2 := by
    rw [h1]

  have h3 : x ^ 2 + y ^ 2 = (1 - x * y) ^ 2 - 2 * (x * y) := by
    have h4 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    rw [h4]
    rw [h1]

  have h4 : x ^ 2 + y ^ 2 = (x * y) ^ 2 - 4 * (x * y) + 1 := by
    nlinarith [h, h3, sq_nonneg (x * y), sq_nonneg (x + y), sq_nonneg (x - y)]

  have eq1 : x * y + 1 / (x * y) - y / x - x / y = ( (x * y) ^ 2 + 1 - x ^ 2 - y ^ 2 ) / (x * y) := by 
    field_simp
    ring
  
  rw [eq1]

  have num_eq : (x * y) ^ 2 + 1 - x ^ 2 - y ^ 2 = 4 * (x * y) := by
    nlinarith [h4, sq_nonneg (x * y), sq_nonneg (x + y), sq_nonneg (x - y)]
  
  have eq2 : ( (x * y) ^ 2 + 1 - x ^ 2 - y ^ 2 ) / (x * y) = 4 := by
    rw [num_eq]
    field_simp
    <;> nlinarith
  
  exact eq2