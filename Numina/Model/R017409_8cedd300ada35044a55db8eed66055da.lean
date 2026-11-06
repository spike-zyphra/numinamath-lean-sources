import Mathlib

theorem algebra_318309 {x y : ℝ} (h : 2*x-2*x^2*y^2-2*y*(x+x^2)-x^2=5) :
    (x, y)=(3, -2/3) := by
  have h1 : (x - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x * y + 3 / 2), sq_nonneg (x - 3), sq_nonneg (y + 2 / 3), 
              sq_nonneg (x * (y + 2 / 3)), sq_nonneg ((x - 3) * (y + 2 / 3)), sq_nonneg (x^2 * y), sq_nonneg ((x - 3) * y)]
  have hx : x = 3 := by
    nlinarith
  have h2 : y = -2 / 3 := by
    rw [hx] at h
    ring_nf at h 
    have h3 : (y + 2 / 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y + 2 / 3)]
    have h4 : y + 2 / 3 = 0 := by 
      apply pow_eq_zero 
      exact h3 
    linarith 
  simp [Prod.ext_iff, hx, h2]