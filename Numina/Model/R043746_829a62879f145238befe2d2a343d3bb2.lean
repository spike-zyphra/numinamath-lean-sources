import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_235290 :
  IsLeast {s | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^2 + y^2 + z^2 = 1 ∧ s = x * y / z + y * z / x + z * x / y} (Real.sqrt 3) := by
  constructor
  · -- Show that sqrt(3) is in the set.
    use 1 / Real.sqrt 3, 1 / Real.sqrt 3, 1 / Real.sqrt 3
    constructor
    · -- x > 0
      positivity
    constructor
    · -- y > 0
      positivity
    constructor
    · -- z > 0
      positivity
    constructor
    · -- x^2 + y^2 + z^2 = 1
      have h1 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      field_simp [h1]
      <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]
    · -- s = x * y / z + y * z / x + z * x / y
      have h1 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      field_simp [h1]
      <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]
      all_goals norm_num
  · -- Show that sqrt(3) is the minimum
    intro s hs
    rcases hs with ⟨x, y, z, hx, hy, hz, h1, he⟩
    have h2 : s = x * y / z + y * z / x + z * x / y := by linarith [he]
    have h4 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
      have h54 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 * ((x * y / z) * (y * z / x) + (x * y / z) * (z * x / y) + (y * z / x) * (z * x / y)) := by
        have h58 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 * ((x * y / z) * (y * z / x) + (x * y / z) * (z * x / y) + (y * z / x) * (z * x / y)) := by
          nlinarith [sq_nonneg (x * y / z - y * z / x), sq_nonneg (x * y / z - z * x / y), sq_nonneg (y * z / x - z * x / y), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos (mul_pos hx hy) hz, sq_nonneg ((x * y / z) - (y * z / x)), sq_nonneg ((x * y / z) - (z * x / y)), sq_nonneg ((y * z / x) - (z * x / y))]
        linarith 
      have h55 : (x * y / z) * (y * z / x) + (x * y / z) * (z * x / y) + (y * z / x) * (z * x / y) = x ^ 2 + y ^ 2 + z ^ 2 := by
        field_simp at *
        ring
      nlinarith [h54, h55, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    have h25 : (x * y / z + y * z / x + z * x / y) ≥ Real.sqrt 3 := by
      have h24 : x * y / z + y * z / x + z * x / y ≥ 0 := by positivity
      have h20 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ (3 : ℝ) := by
        nlinarith [h4, h1]
      have h42 : Real.sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) ≥ Real.sqrt (3 : ℝ) := by
        apply Real.sqrt_le_sqrt
        nlinarith [h20]
      have h43 : Real.sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) = (x * y / z + y * z / x + z * x / y : ℝ) := by
        rw [Real.sqrt_sq (show (x * y / z + y * z / x + z * x / y : ℝ) ≥ 0 by positivity)]
      nlinarith [h42, h43, Real.sqrt_nonneg 3]
    have h33 : s ≥ Real.sqrt 3 := by 
      nlinarith [h2, h25]
    linarith [h33]