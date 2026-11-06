import Mathlib

theorem calculus_22129 {x y : ℝ} (hx : x ≠ 0) (h : !![-7/25, 24/25; 24/25, 7/25].mulVecᵣ ![x, y] = ![x, y]) : y / x = 4 / 3 := by
  have eq1 := congr_arg (λ v => v 0) h
  have eq2 := congr_arg (λ v => v 1) h
  simp [Matrix.mulVecᵣ, Matrix.vecCons, add_mul, mul_add, mul_comm] at eq1 eq2
  have h1 : -7 * x + 24 * y = 25 * x := by 
    linarith
  have h3 : 24 * y = 32 * x := by
    linarith
  have h4 : y / x = 4 / 3 := by
    have hx1 : x ≠ 0 := hx
    have h5 : y = 4 / 3 * x := by
      linarith
    have h6 : y / x = 4 / 3 := by
      rw [show y = 4 / 3 * x by linarith]
      field_simp [hx1]
      <;> linarith
    exact h6
  exact h4