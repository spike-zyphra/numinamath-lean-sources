import Mathlib

theorem algebra_108864 {p q : ℝ} (h : ∃ x y, x ≠ y ∧ x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0 ∧ x = 2 * y) :
    2 * p^2 = 9 * q := by

  rcases h with ⟨x, y, hxy, hx, hy, hx2y⟩

  have h_eq1 : x^2 + p * x + q = 0 := hx
  have h_eq2 : y^2 + p * y + q = 0 := hy
  
  have h_eq3 : x^2 + p * x + q - (y^2 + p * y + q) = 0 := by
    linarith [h_eq1, h_eq2]

  have h_eq4 : (x - y) * (x + y + p) = 0 := by
    nlinarith
  
  cases' (mul_eq_zero.mp h_eq4) with h_eq5 h_eq6
  
  · -- Case: x - y = 0, which implies x = y, detected contradiction
    exfalso
    exact hxy (by linarith)
  
  · -- Case: x + y + p = 0
    have h_eq7 : x + y + p = 0 := by linarith

    rw [show x = 2 * y by linarith [hx2y]] at h_eq7
    have h_eq8 : 3 * y + p = 0 := by linarith

    have h_eq9 : y = -p / 3 := by linarith

    rw [h_eq9] at h_eq2
    nlinarith [h_eq2]