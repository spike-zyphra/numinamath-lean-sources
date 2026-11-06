import Mathlib

theorem algebra_97086 {x y z : ℝ} (h : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0) (h1 : 1 / x - 1 / y = 1 / z) :
    z = x * y / (y - x) := by
  rcases h with ⟨hx, hy, hz⟩
  have h2 : z ≠ 0 := hz
  have h3 : x ≠ 0 := hx
  have h4 : y ≠ 0 := hy
  have eq1 : 1 / x - 1 / y = (y - x) / (x * y) := by
    field_simp [h3, h4]
    <;> ring
  have eq3 : (y - x) * z = x * y := by
    have eq4 : (y - x) / (x * y) = 1 / z := by 
      linarith [h1, eq1]
    field_simp [h3, h4, h2] at eq4 ⊢ 
    <;> linarith
  -- Now prove that $z = \frac{xy}{y - x}$ from $z \neq 0$, $y - x \neq 0$, and $(y - x) * z = x * y$
  have h5 : y - x ≠ 0 := by 
    by_contra h6
    have eq6 : (y - x) * z = x * y := eq3
    rw [show y - x = (0 : ℝ) by linarith [h6]] at eq6
    have eq7 : (0 : ℝ) * z = x * y := by 
      linarith [eq6]
    have eq8 : x * y = 0 := by
      linarith [eq7]
    have eq9 : x ≠ 0 := h3
    have eq10 : y ≠ 0 := h4
    have eq11 : x * y ≠ 0 := by
      apply mul_ne_zero
      exact h3
      exact h4
    contradiction 
  have eq4 : z = x * y / (y - x) := by
    have eq5 : (y - x) * z = x * y := eq3
    have h6 : y - x ≠ 0 := h5
    field_simp [h6] at eq5 ⊢
    <;> linarith 
  exact_mod_cast eq4