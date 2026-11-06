import Mathlib

theorem algebra_300828 {x y : ℤ} (hx : 0 < x) (hy : 0 < y)
    (h1 : x * y + x + y = 71) (h2 : x ^ 2 * y + x * y ^ 2 = 880) :
    x ^ 2 + y ^ 2 = 146 := by
  have eq1 : x * y + (x + y) = 71 := by 
    linarith
  have eq2 : x * y * (x + y) = 880 := by
    nlinarith
  have h3 : (x + y) ^ 2 - 71 * (x + y) + 880 = 0 := by
    have hS1 : x * y = 71 - (x + y) := by 
      linarith
    rw [hS1] at eq2
    nlinarith
  have h4 : (x + y - 16) * (x + y - 55) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- Case where x + y = 16
    have h7 : x + y = 16 := by 
      linarith
    have h8 : x * y = 55 := by 
      nlinarith
    have h9 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by 
      nlinarith
    rw [h7, h8] at h9
    nlinarith
  · -- Case where x + y = 55
    have h10 : x + y = 55 := by 
      linarith
    have h11 : x * y = 16 := by 
      nlinarith
    have h13 : y = 55 - x := by
      omega
    rw [h13] at h11
    have h12 : x ≤ 54 := by
      nlinarith
    have h14 : x ≥ 1 := by 
      nlinarith
    interval_cases x <;> omega