import Mathlib
open Real Set
open scoped BigOperators

/-
22nd ASU 1988 Problem 18 
Find the minimum value of xy/z + yz/x + zx/y for positive reals x, y, z 
with x ^ 2 + y ^ 2 + z ^ 2 = 1.
-/
theorem inequalities_122914 :
  IsLeast {
    t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ 
    x^2 + y^2 + z^2 = 1 ∧ t = x * y / z + y * z / x + z * x / y
  } (Real.sqrt 3) := by
    constructor
    · -- Let's prove that √3 belongs to the set
      use 1 / Real.sqrt 3, 1 / Real.sqrt 3, 1 / Real.sqrt 3
      constructor
      · -- Show x > 0
        positivity
      constructor
      · -- Show y > 0
        positivity
      constructor
      · -- Show z > 0
        positivity
      constructor
      · -- Show x² + y² + z² = 1
        have h1 : (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by
          calc
            (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 ^ 2 / (Real.sqrt 3 ^ 2) := by ring
            _ = 1 / 3 := by norm_num [Real.sq_sqrt]
        linarith [h1]
      · -- Show t = x * y / z + y * z / x + z * x / y
        have h2 : (1 / Real.sqrt 3 : ℝ) * (1 / Real.sqrt 3) / (1 / Real.sqrt 3) = 1 / Real.sqrt 3 := by
          field_simp
        ring_nf
        norm_num [h2, Real.sq_sqrt]
        ring
    · -- Now prove that √3 is the least element in the set
      intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, hxyz, ht⟩
      have h1 : t = x * y / z + y * z / x + z * x / y := ht
      have h2 : t ≥ Real.sqrt 3 := by
        have h3 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := by
          have h4 : (x * y / z + y * z / x + z * x / y) ^ 2 - 3 ≥ 0 := by
            have h5 : (x * y / z + y * z / x + z * x / y) ^ 2 - 3 = (x * y / z) ^ 2 + (y * z / x) ^ 2 + (z * x / y) ^ 2 + 2 * (x^2 + y^2 + z^2) - 3 := by
              field_simp
              ring
            rw [h5]
            have h6 : x^2 + y^2 + z^2 = 1 := hxyz
            nlinarith [sq_nonneg (x * y / z - y * z / x), sq_nonneg (y * z / x - z * x / y), sq_nonneg (z * x / y - x * y / z),
              mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, h6]
          nlinarith
        have h5 : x * y / z + y * z / x + z * x / y ≥ 0 := by
          apply add_nonneg
          apply add_nonneg
          · apply div_nonneg
            · apply mul_nonneg
              · linarith
              · linarith
            · linarith
          · apply div_nonneg
            · apply mul_nonneg
              · linarith
              · linarith
            · linarith
          · apply div_nonneg
            · apply mul_nonneg
              · linarith
              · linarith
            · linarith
        nlinarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num), h3, h5]
      linarith [h1, h2]