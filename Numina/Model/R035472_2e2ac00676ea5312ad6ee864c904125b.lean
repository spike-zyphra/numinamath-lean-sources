import Mathlib

theorem algebra_165899 (x : ℝ) (m p n q : ℝ) (h : x^2 + (2*m*p + 2*n*q)^2 + (2*m*q - 2*n*p)^2 = 
    (m^2 + n^2 + p^2 + q^2)^2) :
    x = m^2 + n^2 - p^2 - q^2 ∨ x = -m^2 - n^2 + p^2 + q^2 := by
  have h1 : x ^ 2 = (m^2 + n^2 - p^2 - q^2) ^ 2 := by
    nlinarith [sq_nonneg (x - (m^2 + n^2 - p^2 - q^2)), sq_nonneg (x + (m^2 + n^2 - p^2 - q^2)), 
      sq_nonneg (m^2 + n^2 - p^2 - q^2), sq_nonneg (m * p - n * q), sq_nonneg (m * q + n * p)]
  have h2 : x ^ 2 - (m^2 + n^2 - p^2 - q^2) ^ 2 = 0 := by
    linarith [h1]
  have h3 : (x - (m^2 + n^2 - p^2 - q^2)) * (x + (m^2 + n^2 - p^2 - q^2)) = 0 := by
    nlinarith [h2]
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case where $x - (m^2 + n^2 - p^2 - q^2) = 0$
    left
    linarith
  · -- Case where $x + (m^2 + n^2 - p^2 - q^2) = 0$
    right
    linarith