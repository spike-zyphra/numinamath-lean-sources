import Mathlib

/-Find $x$, given that \[\dfrac{\sqrt{x}}{x\sqrt{3}+\sqrt{2}} = \dfrac{1}{2x\sqrt{6}+4}.\]-/
theorem algebra_21335 {x : ℝ} (hx : 0 < x) (hx1 : x * Real.sqrt 3 + Real.sqrt 2 ≠ 0) (h : Real.sqrt x / (x * Real.sqrt 3 + Real.sqrt 2) = 1 / (2 * x * Real.sqrt 6 + 4)) :
    x = 1 / 8 := by
  -- first calculate the relation of two denominators
  have eq : 2 * x * Real.sqrt 6 + 4 = 2 * Real.sqrt 2 * (x * Real.sqrt 3 + Real.sqrt 2) := by
    calc
      2 * x * Real.sqrt 6 + 4 = 2 * (x * Real.sqrt 6 + 2) := by ring_nf
      _ = 2 * (x * Real.sqrt (3 * 2) + (Real.sqrt 2) ^ 2) := by rw [Real.sq_sqrt]; norm_num; norm_num
      _ = 2 * Real.sqrt 2 * (x * Real.sqrt 3 + Real.sqrt 2) := by rw [Real.sqrt_mul (show 0 ≤ 3 by norm_num) 2]; ring_nf
  -- show that the denominator is not zero
  have hx2 : 2 * x * Real.sqrt 6 + 4 ≠ 0 := by
    rw [eq]
    contrapose! hx1
    rw [mul_eq_zero] at hx1
    simp at hx1
    exact hx1
  -- simplify the equation
  field_simp [hx, hx1, hx2] at h
  -- simplify the equation to "mul_right_cancel" form
  replace h : (√x * 2 * √2) * (x * √3 + √2) = 1 * (x * √3 + √2) := by
    rw [eq] at h
    ring_nf at h ⊢ 
    exact h
  -- cancel the common factor
  apply mul_right_cancel₀ at h
  pick_goal 2
  exact hx1
  -- show that x = 1 / 8
  calc
    x = x * 8 / 8 := by ring_nf
    _ = √x ^ 2 * 2 * 2 * 2 / 8 := by rw [Real.sq_sqrt]; ring_nf; linarith only [hx]
    _ = √x ^ 2 * 2 * 2 * √2 ^ 2 / 8 := by norm_num
    _ = √x * 2 * √2 * (√x * 2 * √2)  / 8 := by ring_nf
    _ = 1 * 1 / 8 := by rw [h]
    _ = 1 / 8 := by norm_num 