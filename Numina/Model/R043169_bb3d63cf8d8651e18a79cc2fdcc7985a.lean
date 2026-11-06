import Mathlib

theorem number_theory_298547 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z * (x + y + z) = 1) :
    2 ≤ (x + y) * (y + z) := by
  have hx1 : x ≥ 1 := by 
    omega
  have hy1 : y ≥ 1 := by 
    omega
  have hz1 : z ≥ 1 := by 
    omega
  have h1 : x + y + z ≥ 3 := by 
    omega
  have h2 : x * y * z * (x + y + z) ≥ 3 := by
    have h5 : x * y * z ≥ 1 := by
      have h2 : x ≥ 1 := hx1
      have h3 : y ≥ 1 := hy1
      have h4 : z ≥ 1 := hz1
      have h5 : x * y ≥ 1 := by
        nlinarith
      have h6 : x * y * z ≥ 1 := by
        nlinarith
      linarith
    have h6 : x + y + z ≥ 3 := h1
    have h7 : x * y * z * (x + y + z) ≥ 1 * 3 := by 
      have h8 : x * y * z * (x + y + z) = (x * y * z) * (x + y + z) := by
        ring
      rw [h8]
      nlinarith [h5, h6, show 0 < (x + y + z) by nlinarith, show 0 < (x * y * z) by nlinarith]
    linarith
  nlinarith [h, h2, show 0 < x by linarith, show 0 < y by linarith, show 0 < z by linarith]