import Mathlib

theorem algebra_1287 (x : Fin 7 → ℕ) (hx : StrictMono x)
    (h1 : x 0 + x 1 = x 2) (h2 : x 1 + x 2 = x 3)
    (h3 : x 2 + x 3 = x 4) (h4 : x 3 + x 4 = x 5)
    (h5 : x 4 + x 5 = x 6)
    (h6 : x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 = 2010) :
    x 0 + x 1 + x 2 ≤ 236 := by

  have h7 : x 0 < x 1 := by
    apply hx
    simp
  have h8 : x 1 < x 2 := by
    apply hx
    simp
  have h9 : x 2 < x 3 := by
    apply hx
    simp
  have h10 : x 3 < x 4 := by
    apply hx
    simp
  have h11 : x 4 < x 5 := by
    apply hx
    simp
  have h12 : x 5 < x 6 := by
    apply hx
    simp
  have eq1 : x 2 = x 0 + x 1 := by
    omega
  have eq2 : x 3 = x 0 + 2 * x 1 := by 
    omega
  have eq3 : x 4 = 2 * x 0 + 3 * x 1 := by
    omega
  have eq4 : x 5 = 3 * x 0 + 5 * x 1 := by 
    omega
  have eq5 : x 6 = 5 * x 0 + 8 * x 1 := by 
    omega
  rw [eq1, eq2, eq3, eq4, eq5] at h6
  omega