import Mathlib

theorem calculus_22605 (a x : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) (hv : V = !![a + x, a - x, a - x;a - x, a + x, a - x; a - x, a - x, a + x]) :
    V.det = 0 ↔ x = 0 ∨ x = 3 * a := by
  rw [hv]
  simp [Matrix.det_fin_three, Fin.sum_univ_three, mul_add, add_mul]
  constructor
  · -- Suppose determinant is 0, prove x = 0 ∨ x = 3a
    intro h
    have h_eq : 4 * x^2 * (3 * a - x) = 0 := by
      ring_nf at h ⊢
      linarith
    cases' (mul_eq_zero.mp h_eq) with h1 h2
    · -- Case where 4 * x^2 = 0
      have hx2 : x^2 = 0 := by
        linarith
      have hx : x = 0 := by
        rw [sq_eq_zero_iff] at hx2
        linarith
      left
      exact hx
    · -- Case where 3 * a - x = 0
      have hx : x = 3 * a := by
        linarith
      right
      linarith
  · -- Suppose x = 0 ∨ x = 3a, prove determinant is 0
    rintro (hx | hx)
    · -- Case where x = 0
      rw [hx]
      norm_num
    · -- Case where x = 3a
      rw [hx]
      ring_nf