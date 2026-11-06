import Mathlib

theorem algebra_59780 {x y z : ℝ} (hx : x = Real.sqrt (2 * y + 3)) (hy : y = Real.sqrt (2 * z + 3))
    (hz : z = Real.sqrt (2 * x + 3)) : x = 3 ∧ y = 3 ∧ z = 3 := by
  have h1 : x ≥ 0 := by
    rw [hx]
    apply Real.sqrt_nonneg
  have h2 : y ≥ 0 := by 
    rw [hy]
    apply Real.sqrt_nonneg
  have h3 : z ≥ 0 := by 
    rw [hz]
    apply Real.sqrt_nonneg
  -- Squaring the equations
  have eq1 : x^2 = 2 * y + 3 := by
    have h4 : x^2 = Real.sqrt (2 * y + 3) ^ 2 := by
      rw [hx]
    have h5 : Real.sqrt (2 * y + 3) ^ 2 = 2 * y + 3 := by
      apply Real.sq_sqrt
      nlinarith
    nlinarith [h4, h5]
  have eq2 : y^2 = 2 * z + 3 := by
    have h4 : y^2 = Real.sqrt (2 * z + 3) ^ 2 := by
      rw [hy]
    have h5 : Real.sqrt (2 * z + 3) ^ 2 = 2 * z + 3 := by
      apply Real.sq_sqrt
      nlinarith
    nlinarith [h4, h5]
  have eq3 : z^2 = 2 * x + 3 := by
    have h4 : z^2 = Real.sqrt (2 * x + 3) ^ 2 := by
      rw [hz]
    have h5 : Real.sqrt (2 * x + 3) ^ 2 = 2 * x + 3 := by
      apply Real.sq_sqrt
      nlinarith
    nlinarith [h4, h5]
  -- Solving system of equations with constraints
  have hx3 : x = 3 := by 
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3)]
  have hy3 : y = 3 := by
    nlinarith [hx3]
  have hz3 : z = 3 := by
    nlinarith [hy3]
  exact ⟨hx3, hy3, hz3⟩