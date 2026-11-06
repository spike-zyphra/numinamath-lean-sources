import Mathlib

theorem algebra_3536 : IsLeast {t : ℝ | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x * y * z * (x + y + z) = 4 ∧ t = (x + y) * (y + z)} 4 := by
  constructor
  · -- Show 4 is in the set
    use 1, (-3 + Real.sqrt 17) / 2, 2
    constructor
    · norm_num
    constructor
    · -- Show y > 0
      have h1 : Real.sqrt 17 > 0 := by
        apply Real.sqrt_pos.mpr
        norm_num
      have h2 : Real.sqrt 17 > 3 := by
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), sq_nonneg (Real.sqrt 17 - 3)]
      linarith
    constructor
    · norm_num
    constructor
    · -- Show x * y * z * (x + y + z) = 4
      field_simp
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), sq_nonneg (Real.sqrt 17 - 3)]
    · -- Show 4 = (x + y) * (y + z)
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), sq_nonneg (Real.sqrt 17 - 3)]
  · -- Show that 4 is a lower bound
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, h2⟩
    nlinarith [sq_nonneg (x * z - 2), sq_nonneg (y * (x + y + z) - 2), sq_nonneg (x * z - y * (x + y + z)), mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith), mul_pos (show 0 < y * z by nlinarith) (show 0 < x * z by nlinarith)]