import Mathlib

theorem algebra_20292 :
  IsGreatest {u:ℝ | ∃(x y z:ℝ), u = x*y*√10+y*z ∧ x^2+y^2+z^2 = 1 ∧
  0 < x ∧ 0 < y ∧ 0 < z}
  (√11/2) := by
  constructor
  · -- Show that √11/2 is achievable
    use Real.sqrt 10 / Real.sqrt 22, Real.sqrt 11 / Real.sqrt 22, 1 / Real.sqrt 22
    constructor
    · -- Show the value equals to √11/2
      field_simp
      ring_nf
      <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (0 : ℝ) < 10),
          Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num : (0 : ℝ) < 11),
          Real.sqrt_pos.mpr (show (0 : ℝ) < 22 by norm_num : (0 : ℝ) < 22),
          Real.sq_sqrt]
      <;> ring_nf <;> field_simp <;> ring_nf <;> norm_num [Real.sq_sqrt]
      <;> ring_nf <;> norm_num
    constructor
    · -- Show the constraint is satisfied
      field_simp
      ring_nf
      <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (0 : ℝ) < 10),
          Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num : (0 : ℝ) < 11),
          Real.sqrt_pos.mpr (show (0 : ℝ) < 22 by norm_num : (0 : ℝ) < 22),
          Real.sq_sqrt]
      <;> ring_nf <;> field_simp <;> ring_nf <;> norm_num [Real.sq_sqrt]
    constructor
    · -- Show x > 0
      positivity
    constructor
    · -- Show y > 0
      positivity
    · -- Show z > 0
      positivity
  · -- Show that √11/2 is the maximum
    intro u hu
    rcases hu with ⟨x, y, z, heq, hsum, hx, hy, hz⟩
    nlinarith [sq_nonneg (x - (√10 * z)), sq_nonneg (y * √11 - z * 11), sq_nonneg (x * √10 - z * √22), sq_nonneg (y * √22 - √11), sq_nonneg (x * √11 - y * √22), sq_nonneg (√10 * y - √11 * x), Real.sqrt_nonneg 10, Real.sqrt_nonneg 11, Real.sqrt_nonneg 22, Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 22 by norm_num), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (0 : ℝ) < 10), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num : (0 : ℝ) < 11), Real.sqrt_pos.mpr (show (0 : ℝ) < 22 by norm_num : (0 : ℝ) < 22)]