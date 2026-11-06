import Mathlib

theorem algebra_310877 (l w h : ℝ) (hw : w > 0) (hw' : l > 0) (hw'' : h > 0)
    (hvol : l * w * h = 8) (hsurf : 2 * (l * w + w * h + l * h) = 32)
    (hge : ∃ r, w = l * r ∧ h = w * r) :
    4 * (l + w + h) = 32 := by
  rcases hge with ⟨r, hw_eq, hh_eq⟩
  have hw_eq2 : w = l * r := hw_eq
  have h_eq : h = l * r^2 := by
    rw [hh_eq, hw_eq2]
    <;> ring_nf <;> nlinarith 
  have hw_eq3 : (l * r) ^ 3 = 8 := by
    rw [show w = l * r by linarith [hw_eq2], show h = l * r^2 by linarith [h_eq]] at hvol
    nlinarith 
  have hw_eq4 : l * r = 2 := by
    have h1 : (l * r) ^ 3 - 8 = 0 := by 
      linarith
    have h2 : (l * r - 2) * ((l * r) ^ 2 + 2 * (l * r) + 4) = 0 := by
      ring_nf at h1 ⊢
      linarith
    cases' (mul_eq_zero.mp h2) with h3 h4 
    · -- Case l * r - 2 = 0, so l * r = 2
      linarith 
    · -- Case (l * r)^2 + 2 * (l * r) + 4 = 0
      nlinarith [sq_nonneg ((l * r) + 1)]
  have hw2 : w = 2 := by
    nlinarith [hw_eq4, hw_eq2]
  have h_eq1 : l * h = 4 := by
    rw [hw2] at hvol 
    nlinarith 
  have h_eq2 : l + h = 6 := by
    rw [hw2] at hsurf 
    nlinarith 
  linarith [hw2, h_eq1, h_eq2]