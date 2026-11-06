import Mathlib

theorem algebra_173241 (x y z : ℝ) (h₀ : x ≠ y) (h₁ : y ≠ z) (h₂ : z ≠ x)
    (h₃ : x^2 + y^2 = -x + 3 * y + z) (h₄ : y^2 + z^2 = x + 3 * y - z)
    (h₅ : x^2 + z^2 = 2 * x + 2 * y - z) :
    (x, y, z) = (-3 / 2, 5 / 2, -1 / 2) ∨ (x, y, z) = (0, 1, -2) := by
  have eq1 : x^2 - z^2 = -2 * x + 2 * z := by
    nlinarith
  have eq2 : x + z = -2 := by
    have h3 : x - z ≠ 0 := by
      intro h
      apply h₂
      linarith
    have eq3 : (x - z) * (x + z + 2) = 0 := by
      ring_nf at eq1 ⊢
      nlinarith
    cases' (mul_eq_zero.1 eq3) with h4 h5
    · -- x - z = 0
      exfalso
      apply h₂
      linarith
    · -- x + z + 2 = 0
      linarith
  have eq3 : y^2 - x^2 = -x + y := by
    nlinarith
  have eq4 : y + x = 1 := by
    have h4 : y - x ≠ 0 := by
      intro h
      apply h₀
      linarith
    have eq5 : (y - x) * (y + x - 1) = 0 := by
      ring_nf at eq3 ⊢
      nlinarith
    cases' (mul_eq_zero.1 eq5) with h4 h5
    · -- y - x = 0
      exfalso
      apply h₀
      linarith
    · -- y + x - 1 = 0
      linarith
  have eq5 : z = -2 - x := by
    linarith [eq2]
  have eq6 : y = 1 - x := by
    linarith [eq4]
  rw [eq6, eq5] at h₃
  have h6 : x * (2 * x + 3) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- Case x = 0
    have hx : x = 0 := by
      linarith
    have hy : y = 1 := by
      rw [hx] at eq6
      linarith
    have hz : z = -2 := by
      rw [hx] at eq5
      linarith
    right
    simp [hx, hy, hz]
  · -- Case 2x + 3 = 0
    have hx : x = -3 / 2 := by
      linarith
    have hy : y = 5 / 2 := by
      rw [hx] at eq6
      linarith
    have hz : z = -1 / 2 := by
      rw [hx] at eq5
      linarith
    left
    simp [hx, hy, hz]