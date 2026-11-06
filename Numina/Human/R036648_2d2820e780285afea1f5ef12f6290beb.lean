import Mathlib

/-Simplify and rationalize the denominator: $$\frac{8}{3\sqrt{3}+ 7\sqrt{27}}.$$-/
theorem algebra_20540 : 8 / (3 * Real.sqrt 3 + 7 * Real.sqrt 27) = Real.sqrt 3 / 9 := by
  calc
    8 / (3 * Real.sqrt 3 + 7 * Real.sqrt 27) = 8 / (3 * Real.sqrt 3 + 7 * Real.sqrt (3 ^ 2 * 3)) := by norm_num
    -- simplify to 8 / (24 * √3)
    _ = 8 / (3 * Real.sqrt 3 + 7 * (3 * Real.sqrt 3)) := by field_simp
    _ = 8 / (24 * Real.sqrt 3) := by ring_nf
    -- simplify to √3 / 9
    _ = 1 / (3 * √3) := by field_simp; ring_nf
    _ = 3 / (9 * √3) := by field_simp; ring_nf
    _ = √3 * (√3 / (9 * √3)) := by ring_nf; rw [Real.sq_sqrt]; ring_nf; norm_num
    _ = √3 / 9 := by rw [div_mul_cancel_right₀]; ring_nf; positivity
