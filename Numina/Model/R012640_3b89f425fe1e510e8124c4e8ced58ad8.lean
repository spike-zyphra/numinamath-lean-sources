import Mathlib

theorem algebra_197213 (x y : ℝ) :
    x^3 + y^2 + x + 1 = 0 ∧ y^3 + x^2 + y + 1 = 0 ↔ (x, y) = (-1, -1) := by
  constructor
  · -- Assume both equations hold, prove (x, y) = (-1, -1)
    rintro ⟨h1, h2⟩
    have h10 : x^3 - y^3 + y^2 - x^2 + x - y = 0 := by
      nlinarith 
    have eq1 : (x - y) * (x^2 + y^2 + x * y - x - y + 1) = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x + 1), sq_nonneg (y + 1)]

    cases' (mul_eq_zero.mp eq1) with h_eq2 h_eq3
    · -- Case where (x - y) * ... =0. So x=y.
      have hx : x = y := by linarith
      rw [show y = x by linarith [hx]] at h1
      have hx2 : (x + 1) * (x^2 + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp hx2) with hx3 hx4
      · -- Case where x+1 =0
        have hx4 : x = -1 := by linarith
        have hy4 : y = -1 := by linarith [hx4, hx]
        simp [hx4, hy4]
      · -- Case where x^2 +1 =0 
        exfalso 
        nlinarith [sq_nonneg x]
    · -- Case where second part of mul_eq_zero is true.
      exfalso
      -- Now proving False for the case x^2 + y^2 + x*y - x - y + 1=0.
      -- This expresses that a sum of squares is non-positive. But must be > 0
      have h3 : x^2 + y^2 + x * y - x - y + 1 > 0 := by
        nlinarith [sq_nonneg (x + (y - 1) / 2), sq_nonneg (y - 1 / 3), sq_nonneg (x - 1 / 3), sq_nonneg (x - y)]
      have h4 : x^2 + y^2 + x * y - x - y + 1 = 0 := by linarith
      linarith
  · -- Assume (x, y) = (-1, -1)
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    · norm_num