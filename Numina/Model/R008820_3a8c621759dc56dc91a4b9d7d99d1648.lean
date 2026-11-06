import Mathlib

theorem algebra_10239 {p q : ℝ} (hp : p ≠ q) (h : (p - 5) * (2 * p + 9) = p ^ 2 - 13 * p + 40)
    (hq : (q - 5) * (2 * q + 9) = q ^ 2 - 13 * q + 40) :
    (p + 3) * (q + 3) = -112 := by

  have h1 : p^2 + 12 * p - 85 = 0 := by 
    nlinarith

  have h2 : q^2 + 12 * q - 85 = 0 := by 
    nlinarith
  
  have h3 : p + q = -12 := by
    have h3 : p^2 + 12 * p - 85 - (q^2 + 12 * q - 85) = 0 := by 
      linarith [h1, h2]
    have h4 : (p - q) * (p + q + 12) = 0 := by
      nlinarith

    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- Case p - q = 0, so p = q
      exfalso
      exact hp (by linarith)
    · -- Case p + q + 12 = 0, so p + q = -12
      linarith
  
  have h4 : p * q = -85 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hp), h1, h2, h3]

  nlinarith [h3, h4]