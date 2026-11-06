import Mathlib

open EuclideanDomain

theorem number_theory_174305 (z : ℤ) (hz : z % 10 = 7) (h : 7 * 10 ^ 21 + z / 10 = 7 * z) :
    z = 1014492753623188405797 := by
  have h1 : z % 10 = 7 := hz
  have h2 : z = 10 * (z / 10) + 7 := by
    omega
  have h3 : 7 * 10 ^ 21 + z / 10 = 7 * z := by
    linarith [h]
  have h4 : 69 * (z / 10) = 7 * 10 ^ 21 - 49 := by 
    have eq1 : z = 10 * (z / 10) + 7 := h2
    rw [eq1] at h3
    linarith
  have h5 : z / 10 = 101449275362318840579 := by
    omega
  have h7 : z = 1014492753623188405797 := by 
    omega
  linarith [h7]