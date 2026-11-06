import Mathlib

theorem algebra_608894  (x y : ℝ) (h: x^2 * y = 3) (h': x + x*y = 4) : ((x= 1) ∧ (y = 3)) ∨ ((x= 3) ∧ (y = 1/3)) := by
  have eq1 : x ≠ 0 := by
    by_contra h1
    have h2 : x = 0 := h1
    rw [h2] at h h'
    nlinarith
  have eq3 : y = (4 - x) / x := by 
    have h1 : x ≠ 0 := eq1
    field_simp 
    nlinarith 
  rw [eq3] at h 
  have h1 : x * (4 - x) = 3 := by 
    have h2 : x ≠ 0 := eq1
    have eq4 : x ^ 2 * ((4 - x) / x) = x * (4 - x) := by 
      field_simp [h2]
      <;> nlinarith 
    nlinarith [eq4, h]
  have h2 : x^2 - 4 * x + 3 = 0 := by 
    nlinarith 
  have h3 : (x - 1) * (x - 3) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5 
  · -- Case $x - 1 = 0$, so $x = 1$
    have hx1 : x = 1 := by linarith
    have hy1 : y = 3 := by 
      rw [hx1] at eq3 
      field_simp [hx1, eq1] at eq3 ⊢ 
      <;> linarith 
    left 
    exact ⟨hx1, hy1⟩ 
  · -- Case $x - 3 = 0$, so $x = 3$
    have hx2 : x = 3 := by linarith
    have hy2 : y = 1 / 3 := by 
      rw [hx2] at eq3 
      field_simp [hx2, eq1] at eq3 ⊢ 
      <;> linarith 
    right 
    exact ⟨hx2, hy2⟩