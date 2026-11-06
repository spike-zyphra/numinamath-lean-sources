import Mathlib

theorem number_theory_145378 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : (x + y)^2 + 3 * x + y + 1 = z^2) :
    (x, y, z) = (x, x, 2 * x + 1) := by

  have h1 : z > x + y := by 
    nlinarith [h, sq_nonneg (z - (x + y) : ℤ)]
  
  have h2 : (z - (x + y)) * (z + (x + y)) = 3 * x + y + 1 := by 
    nlinarith
  
  have h3 : z - (x + y) > 0 := by 
    nlinarith
  
  set d := z - (x + y) with h4
  have h4' : z = x + y + d := by
    omega
  
  have h5 : d * (2 * (x + y) + d) = 3 * x + y + 1 := by 
    rw [h4'] at h2 
    nlinarith
  
  have h6 : d = 1 := by
    have eq1 : d * (2 * (x + y) + d) = 3 * x + y + 1 := h5
    have h7 : d ≤ 3 := by 
      nlinarith [sq_nonneg ((d - 1) : ℤ), sq_nonneg ((x - y) : ℤ), sq_nonneg ((2 * x - y) : ℤ)]
    have h8 : d > 0 := by 
      linarith
    interval_cases d <;> nlinarith
  
  -- Now from h6 (d=1) prove y =x.
  have h6' : y = x := by 
    rw [h6] at h5
    nlinarith
  
  have h8 : z = 2 * x + 1 := by 
    nlinarith [h4', h6', h6]

  have h9 : (x, y, z) = (x, x, 2 * x + 1) := by
    simp [show y = x by linarith, show z = 2 * x + 1 by linarith]

  exact h9