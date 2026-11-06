import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_221930 :
  IsLeast {n | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ n = (x^2 + y^2 + z^2) / (x * y + y * z)} (Real.sqrt 2) := by
  constructor
  · -- Show sqrt 2 is in the set.
    use 1, Real.sqrt 2, 1
    constructor
    · norm_num
    constructor
    · positivity
    constructor
    · positivity
    · -- Verify that (1^2 + (sqrt 2)^2 + 1^2) / (1 * sqrt 2 + sqrt 2 * 1) = sqrt 2.
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp [show Real.sqrt 2 + Real.sqrt 2 = 2 * Real.sqrt 2 by ring, show Real.sqrt 2 ≠ 0 by positivity, h1]
      <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  · -- Show that sqrt 2 is minimal.
    intro n hn
    rcases hn with ⟨x, y, z, hx, hy, hz, hn⟩
    have h1 : (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z) ≥ Real.sqrt 2 := by
      have h2 : x * y + y * z > 0 := by
        have hx1 : x > 0 := hx
        have hy1 : y > 0 := hy
        have hz1 : z > 0 := hz
        nlinarith [mul_pos hx1 hy1, mul_pos hy1 hz1]
      have h3 : x ^ 2 + y ^ 2 + z ^ 2 ≥ Real.sqrt 2 * (x * y + y * z) := by 
        nlinarith [sq_nonneg (x - z), sq_nonneg (y - Real.sqrt 2 / 2 * (x + z)), sq_nonneg (x * z - y * (Real.sqrt 2 / 2)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sqrt 2 * (x - z)), sq_nonneg (y ^ 2 - 2), mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
      have h4 : (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z) ≥ Real.sqrt 2 := by
        apply (le_div_iff₀ (by positivity)).mpr
        linarith
      exact h4
    linarith [hn, h1]