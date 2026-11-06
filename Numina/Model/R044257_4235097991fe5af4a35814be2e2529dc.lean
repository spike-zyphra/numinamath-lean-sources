import Mathlib

theorem Algebra_609899 {p q : ℝ} (h1 : p + q = 5 / 6) (h2 : p ^ 2 + q ^ 2 + 1 / 36 = 1 / 2) (hpq : p ≥ q) :
  p = 2/3 := by 
  have h3 : p * q = 1 / 9 := by 
    nlinarith 
  have hsq : (p - q) ^ 2 = 1 / 4 := by
    have h7 : (p - q) ^ 2 = (p + q) ^ 2 - 4 * (p * q) := by
      ring
    rw [h7]
    rw [h1]
    rw [h3]
    norm_num 
  have h8 : p - q ≥ 0 := by
    linarith
  have h9 : p - q = 1 / 2 := by 
    have h10 : (p - q) ^ 2 = 1 / 4 := hsq 
    have h11 : p - q ≥ 0 := h8
    nlinarith 
  nlinarith