import Mathlib

open Polynomial Real

theorem algebra_137041 {x y z : ℝ} (h1 : x + y + z = 3) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 3)
    (h3 : x ^ 5 + y ^ 5 + z ^ 5 = 3) : x = 1 ∧ y = 1 ∧ z = 1 := by

  have h4 : x * y + y * z + z * x = 3 := by
    have eq1 : x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by
      ring
    rw [h1] at eq1
    linarith
  
  have h6 : x * y * z = 1 := by
    have eq1 : x ^ 3 + y ^ 3 + z ^ 3 = 3 * (x * y * z) := by
      have h51 : x ^ 3 + y ^ 3 + z ^ 3 = (x + y + z) ^ 3 - 3 * (x + y + z) * (x * y + y * z + z * x) + 3 * (x * y * z) := by
        ring
      rw [h1, h4] at h51
      linarith
    have eq2 : x ^ 4 + y ^ 4 + z ^ 4 = (x + y + z) * (x ^ 3 + y ^ 3 + z ^ 3) - (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2) + (x * y * z) * (x + y + z) := by 
      ring
    have eq3 : x ^ 5 + y ^ 5 + z ^ 5 = (x + y + z) * (x ^ 4 + y ^ 4 + z ^ 4) - (x * y + y * z + z * x) * (x ^ 3 + y ^ 3 + z ^ 3) + (x * y * z) * (x ^ 2 + y ^ 2 + z ^ 2) := by 
      ring
    rw [h1, h4, h2] at eq2
    rw [h1, h4, h2, eq1] at eq3
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]

  have eq2 : (x - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      h1, h4, h3, h6]

  have hx1 : x - 1 = 0 := by 
    apply pow_eq_zero 
    exact eq2
  have h7 : x = 1 := by 
    linarith

  have eq3 : (y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      h1, h4, h3, h6]

  have hy1 : y - 1 = 0 := by 
    apply pow_eq_zero 
    exact eq3
  have h8 : y = 1 := by 
    linarith

  have eq4 : (z - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      h1, h4, h3, h6]

  have hz1 : z - 1 = 0 := by 
    apply pow_eq_zero 
    exact eq4
  have h9 : z = 1 := by 
    linarith

  exact ⟨h7, h8, h9⟩