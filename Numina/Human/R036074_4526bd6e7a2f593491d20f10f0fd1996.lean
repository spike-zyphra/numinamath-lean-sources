import Mathlib
/-find all real numbers x,y,z satisfying
(x+1)yz=12, (y+1)zx=4,(z+1)xy=4 -/
theorem algebra_142615 {x y z : ℝ} (h1 : (x + 1) * y * z = 12) (h2 : (y + 1) * z * x = 4) (h3 : (z + 1) * x * y = 4) :
    (x, y, z) = (2, -2, -2) ∨ (x, y, z) = (1 / 3, 3, 3) := by
 --first show z = y
  have h4 : z = y := by
    have h5 : (y + 1) * z * x ≠ 0 := by
      by_contra h
      nlinarith [sq_nonneg (y + 1), sq_nonneg (z * x), h2]
    have h6 : (z + 1) * x * y ≠ 0 := by
      by_contra h
      nlinarith [sq_nonneg (z + 1), sq_nonneg (x * y), h3]
    have h7 : (y + 1) * z * x = (z + 1) * x * y := by
      nlinarith [h2, h3]
    have h8 : (y + 1) * z * x - (z + 1) * x * y = 0 := by
      linarith
    have h9 : x * (z - y) = 0 := by
      ring_nf at h8 ⊢
      linarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- x = 0
      exfalso
      have h12 : x = 0 := by linarith
      have h13 : (y + 1) * z * x = 0 := by
        rw [h12]
        ring
      have h14 : (y + 1) * z * x ≠ 0 := h5
      contradiction
    · -- z - y = 0
      linarith
  --derive y
  have h5 : (y + 2) * (y + 2) * (y - 3) = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 1 / 3), sq_nonneg (y + 2), sq_nonneg (y - 3), sq_nonneg (z + 2), sq_nonneg (z - 3),
              h1, h2, h3, h4]
  cases' (mul_eq_zero.mp h5) with h6 h7
  cases' (mul_eq_zero.mp h6) with h8 h9
  · -- y + 2 = 0
    have hy : y = -2 := by linarith
    have hz : z = -2 := by linarith [h4, hy]
    have hx : x = 2 := by
      nlinarith [h2, hy, hz]
    left
    exact Prod.ext hx (Prod.ext hy hz)
  · -- y + 2 = 0
    have hy : y = -2 := by linarith
    have hz : z = -2 := by linarith [h4, hy]
    have hx : x = 2 := by
      nlinarith [h2, hy, hz]
    left
    exact Prod.ext hx (Prod.ext hy hz)
  · -- y - 3 = 0
    have hy : y = 3 := by linarith
    have hz : z = 3 := by linarith [h4, hy]
    have hx : x = 1 / 3 := by
      nlinarith [h2, hy, hz]
    right
    exact Prod.ext hx (Prod.ext hy hz)
    