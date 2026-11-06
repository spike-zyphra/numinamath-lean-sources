import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_177901 :
  IsLeast {s | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^2 + y^2 + z^2 = 1 ∧ s = x * y / z + y * z / x + z * x / y} (Real.sqrt 3) := by
  constructor
  · -- √3 can be attained, by x=y=z
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3
    constructor
    · -- Show that sqrt(3)/3 > 0
      have h2 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      positivity
    constructor
    · -- Show that sqrt(3)/3 > 0
      have h2 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      positivity
    constructor
    · -- Show that sqrt(3)/3 > 0
      have h2 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      positivity
    constructor
    · -- Show that (sqrt(3)/3)^2 + (sqrt(3)/3)^2 + (sqrt(3)/3)^2 = 1
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith
    · -- Show that s = sqrt(3)
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 3, h1]
  · -- √3 is the least such value
    intro s hs
    rcases hs with ⟨x, y, z, hx, hy, hz, h1, hs⟩
    have h2 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := by
      have h4 : (x * y / z + y * z / x + z * x / y) ^ 2 =
          (x * y / z) ^ 2 + (y * z / x) ^ 2 + (z * x / y) ^ 2 + 2 * ((x * y / z) * (y * z / x) + (x * y / z) * (z * x / y) + (y * z / x) * (z * x / y)) := by 
        ring
      have h5 : (x * y / z) * (y * z / x) = y ^ 2 := by 
        field_simp
        <;> ring_nf
      have h6 : (x * y / z) * (z * x / y) = x ^ 2 := by 
        field_simp
        <;> ring_nf
      have h7 : (y * z / x) * (z * x / y) = z ^ 2 := by 
        field_simp
        <;> ring_nf
      rw [h4, h5, h6, h7]
      nlinarith [sq_nonneg (x * y / z - y * z / x), sq_nonneg (y * z / x - z * x / y), sq_nonneg (z * x / y - x * y / z),
                sq_nonneg (x^2 + y^2 + z^2 - 1), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
                ]
    have h3 : (x * y / z + y * z / x + z * x / y) ≥ Real.sqrt 3 := by
      have h4 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := by linarith [h2]
      have h5 : (x * y / z + y * z / x + z * x / y) ≥ 0 := by positivity
      have h5' : Real.sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) ≥ Real.sqrt (3 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith [h4]
      have h5'' : Real.sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) = (x * y / z + y * z / x + z * x / y) := by
        rw [Real.sqrt_sq (show (x * y / z + y * z / x + z * x / y) ≥ 0 by positivity)]
      linarith [h5', h5'']
    linarith [hs, h3]