import Mathlib

theorem algebra_313293 {x y z : ℝ} (hxyz : x * y * z = 1) (hsum : x + y + z = 2)
    (hsumsq : x^2 + y^2 + z^2 = 3) :
    1 / (x * y + z - 1) + 1 / (y * z + x - 1) + 1 / (z * x + y - 1) = -2 / 3 := by

  have h1 : x * y + y * z + z * x = 1 / 2 := by
    have h2 : x + y + z = 2 := hsum
    have h3 : x^2 + y^2 + z^2 = 3 := hsumsq
    have h4 : x * y + y * z + z * x = 1 / 2 := by 
      have h5 : x^2 + y^2 + z^2 = (x + y + z)^2 - 2 * (x * y + y * z + z * x) := by 
        nlinarith
      rw [h2] at h5 
      linarith 
    linarith

  have h2 : x * y + z - 1 ≠ 0 := by
    by_contra h 
    have h_eq1 : x * y + z = 1 := by linarith
    -- Now, we need to reach a contradiction using hypotheses
    have eq1a : z = 2 - x - y := by linarith [hsum]
    have eq2 : x + y - x * y = 1 := by 
      rw [eq1a] at h_eq1 
      nlinarith
    have eq4 : x * y * z = 1 := hxyz
    have eq5 : z = 2 - x - y := by linarith [hsum]
    rw [show z = 2 - x - y by linarith] at eq4 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y * z -1)]

  have h3 : y * z + x - 1 ≠ 0 := by 
    by_contra h 
    have h_eq1 : y * z + x = 1 := by linarith 
    have eq1a : x = 2 - y - z := by linarith [hsum]
    have eq2 : y + z - y * z = 1 := by 
      rw [eq1a] at h_eq1 
      nlinarith 
    have eq4 : x * y * z = 1 := hxyz
    have eq5 : x = 2 - y - z := by linarith [hsum]
    rw [show x = 2 - y - z by linarith] at eq4 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y * z -1)]

  have h4 : z * x + y - 1 ≠ 0 := by 
    by_contra h 
    have h_eq1 : z * x + y = 1 := by linarith
    have eq1a : y = 2 - x - z := by linarith [hsum]
    have eq2 : x + z - x * z = 1 := by 
      rw [eq1a] at h_eq1 
      nlinarith 
    have eq4 : x * y * z = 1 := hxyz
    have eq5 : y = 2 - x - z := by linarith [hsum]
    rw [show y = 2 - x - z by linarith] at eq4 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y * z -1)]

  field_simp [h2, h3, h4]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x) ]