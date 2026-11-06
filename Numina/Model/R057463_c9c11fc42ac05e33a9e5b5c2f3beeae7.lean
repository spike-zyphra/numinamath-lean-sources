import Mathlib

theorem algebra_180716 {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : 2 * x = y) (h2 : 3 * z = 2 * x ^ 2) (h3 : x * y = 3 * x * z) :
    x = 1 := by
  rw [show y = 2 * x by linarith [h1]] at h3
  have hz' : z = (2 * x^2) / 3 := by
    nlinarith [h2]

  rw [hz'] at h3
  have h4 : 2 * x^2 = 2 * x^3 := by
    nlinarith
  
  have h5 : x^2 * (1 - x) = 0 := by
    nlinarith [h4]

  cases' (mul_eq_zero.mp h5) with h6 h7

  · -- if x^2 = 0, then x = 0, which implies y = 0, contradicts to hy : y ≠ 0
    have hx : x = 0 := by
      nlinarith

    have h8 : 2 * x = 0 := by 
      nlinarith [hx]

    have h9 : y = 0 := by
      nlinarith [h1, h8]

    contradiction
  
  · -- if 1 - x = 0, so x = 1
    linarith