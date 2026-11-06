import Mathlib

theorem calculus_23314 (x : ℝ) :
    Matrix.det !![1, 1, 1; x, 7, -2; x^3, 343, -8] = 0 ↔ x = 7 ∨ x = -2 ∨ x = -5 := by
  simp [Matrix.det_fin_three]
  constructor
  · -- Forward direction: determinant equals zero implies x values
    intro h
    have eq1 : -9 * x^3 + 351 * x + 630 = 0 := by
      linarith
    have eq2 : x^3 - 39 * x - 70 = 0 := by
      linarith
    have h1 : x^3 - 39 * x - 70 = (x - 7) * (x + 2) * (x + 5) := by 
      ring_nf
    rw [h1] at eq2
    cases' (mul_eq_zero.mp eq2) with h2 h3
    cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case $x - 7 = 0$, so $x = 7$
      left
      linarith
    · -- Case $x + 2 = 0$, so $x = -2$
      right
      left
      linarith
    · -- Case $x + 5 = 0$, so $x = -5$
      right
      right
      linarith
  · -- Backward direction: x values imply determinant equals zero
    rintro (h | h | h)
    · -- Case $x = 7$
      rw [h]
      norm_num
    · -- Case $x = -2$
      rw [h]
      norm_num
    · -- Case $x = -5$
      rw [h]
      norm_num