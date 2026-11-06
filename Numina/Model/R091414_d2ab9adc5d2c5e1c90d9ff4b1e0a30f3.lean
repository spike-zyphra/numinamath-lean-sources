import Mathlib

theorem algebra_11727 {x y : ℤ} (hx : x > 0) (hy : y > 0)
    (hxy : x - y = 6) (hxy1 : x * y = 112) :
    x + y = 22 := by
  have h1 : x = y + 6 := by 
    linarith
  rw [h1] at hxy1
  have h2 : y = 8 := by
    have h3 : y ^ 2 + 6 * y - 112 = 0 := by
      nlinarith
    have h4 : (y + 14) * (y - 8) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Solve y + 14 = 0 to get y = -14 which contradicts y > 0
      nlinarith
    · -- Solve y - 8 = 0, which gives y = 8 that is acceptable.
      nlinarith
  have hx' : x = 14 := by
    linarith [h2, h1]
  nlinarith [hx', h2]