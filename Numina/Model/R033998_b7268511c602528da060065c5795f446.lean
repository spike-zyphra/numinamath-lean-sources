import Mathlib

theorem algebra_135963 {x y : ℝ} (h1 : x^5 + y^5 = 33) (h2 : x + y = 3) :
    (x, y) = (1, 2) ∨ (x, y) = (2, 1) := by
  have h3 : y = 3 - x := by linarith 
  rw [h3] at h1
  have h4 : (x - 1) * (x - 2) = 0 := by 
    ring_nf at h1 
    have h5 : x^4 - 6 * x^3 + 18 * x^2 - 27 * x + 14 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 3 * x + 7), sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x * (x - 1) * (x - 2)), sq_nonneg ((x - 1) * (x - 2)), sq_nonneg (x - 1), sq_nonneg (x - 2)]
    have h6 : (x - 1) * (x - 2) * (x^2 - 3 * x + 7) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case (x - 1) * (x - 2) = 0
      linarith 
    · -- Case x^2 - 3 * x + 7 = 0
      nlinarith [sq_nonneg (x - 3 / 2)]
  cases' (mul_eq_zero.mp h4) with h8 h9
  · -- Case x - 1 = 0, so x = 1
    left
    have hx : x = 1 := by linarith
    have hy : y = 2 := by linarith [h3, hx]
    simp [hx, hy]
  · -- Case x - 2 = 0, so x = 2
    right
    have hx : x = 2 := by linarith
    have hy : y = 1 := by linarith [h3, hx]
    simp [hx, hy]