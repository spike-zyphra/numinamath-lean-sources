import Mathlib
/-Find the number of different positive integer triples $(x, y,z)$ satisfying the equations
$x^2 + y -z = 100$ and $x + y^2 - z = 124$:-/
theorem algebra_68918 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x^2 + y - z = 100) (h2 : x + y^2 - z = 124) :
    (x, y, z) = (12, 13, 57) := by
  
  have h3 : (y - x) * (y + x - 1) = 24 := by
    nlinarith
  
  have h4 : y - x ≥ 0 := by nlinarith [sq_nonneg (y - x), sq_nonneg (y + x - 1)]
  
  have h5 : y - x ≤ 24 := by nlinarith
  
  have h6 : y - x = 1 ∨ y - x = 2 ∨ y - x = 3 ∨ y - x = 4 ∨ y - x = 6 ∨ y - x = 8 ∨ y - x = 12 ∨ y - x = 24 := by 
    have h : (y - x) ∣ 24 := by 
      use (y + x - 1)
      linarith
    have h' : (y - x) ≤ 24 := by nlinarith
    interval_cases (y - x) <;> tauto
  
  rcases h6 with h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
  
  · -- Case y - x = 1
    have hy_mx : y - x = 1 := h7
    have h15 : y + x - 1 = 24 := by 
      rw [hy_mx] at h3
      linarith
    have h16 : y + x = 25 := by linarith
    have hy_eq : y = 13 := by 
      have h1 : y + x = 25 := h16
      have h2 : y - x = 1 := hy_mx
      omega
    have hx_eq : x = 12 := by 
      omega
    have hz_eq : z = 57 := by 
      rw [hx_eq, hy_eq] at h1
      linarith
    exact Prod.ext hx_eq (Prod.ext hy_eq hz_eq)
  
  · -- Case y - x = 2
    have hy_mx : y - x = 2 := h8
    have h15 : y + x - 1 = 12 := by 
      rw [hy_mx] at h3
      linarith
    have h16 : y + x = 13 := by linarith
    have : (y : ℤ) = 15 / 2 := by 
      omega
    omega
  
  · -- Case y - x = 3
    have hy_mx : y - x = 3 := h9
    have h15 : y + x - 1 = 8 := by 
      rw [hy_mx] at h3
      linarith
    have h16 : y + x = 9 := by linarith
    have hy_eq : y = 6 := by 
      omega
    have hx_eq : x = 3 := by 
      omega
    have hz_eq : z = -85 := by 
      rw [hx_eq, hy_eq] at h1
      linarith
    linarith [hz, hz_eq]
  
  · -- Case y - x = 4
    have hy_mx : y - x = 4 := h10
    have h15 : y + x - 1 = 6 := by 
      rw [hy_mx] at h3
      linarith
    have h16 : y + x = 7 := by linarith
    have : (y : ℤ) = 11 / 2 := by 
      omega
    omega
  
  · -- Case y - x = 6
    have hy_mx : y - x = 6 := h11
    have h15 : y + x - 1 = 4 := by 
      rw [hy_mx] at h3
      linarith
    have h16 : y + x = 5 := by linarith
    have : (y : ℤ) = 11 / 2 := by 
      omega
    omega
  
  · -- Case y - x = 8
    have hy_mx : y - x = 8 := h12
    have h15 : y + x - 1 = 3 := by 
      rw [hy_mx] at h3
      linarith
    have h16 : y + x = 4 := by linarith
    have h17 : x < 0 := by 
      omega
    linarith [hx, h17]
  
  · -- Case y - x = 12
    have hy_mx : y - x = 12 := h13
    have h15 : y + x - 1 = 2 := by 
      rw [hy_mx] at h3
      linarith
    have h16 : y + x = 3 := by linarith
    have : (y : ℤ) = 15 / 2 := by 
      omega
    omega
  
  · -- Case y - x = 24
    have hy_mx : y - x = 24 := h14
    have h15 : y + x - 1 = 1 := by 
      rw [hy_mx] at h3
      linarith
    have h16 : y + x = 2 := by linarith
    have h17 : x < 0 := by 
      omega
    linarith [hx, h17]