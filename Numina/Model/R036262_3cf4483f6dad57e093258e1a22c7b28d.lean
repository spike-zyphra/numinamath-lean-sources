import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_304091 :
  IsLeast {u : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
    u = (sqrt (x^2 + y^2 + x * y) + sqrt (y^2 + z^2 + y * z) +
          sqrt (z^2 + x^2 + z * x)) / (x + y + z)} (sqrt 3) := by
  constructor
  · -- Show sqrt 3 is in the set.
    use 1, 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show not all zero
      norm_num
    · -- Show the value is sqrt 3
      have h1 : (1: ℝ) + (1: ℝ) + (1: ℝ) = (3: ℝ) := by norm_num
      have h2 : sqrt ((1: ℝ) ^ 2 + (1: ℝ) ^ 2 + (1: ℝ) * (1: ℝ)) = sqrt 3 := by
        norm_num
      rw [h1]
      rw [h2]
      field_simp
      <;> ring_nf <;> norm_num
  · -- Show sqrt 3 is the least
    intro u hu
    rcases hu with ⟨x, y, z, hx, hy, hz, hne, heq⟩
    have h1 : x + y + z > 0 := by
      by_contra h
      push_neg at h
      have h2 : x = 0 := by nlinarith [show 0 ≤ x by linarith, show 0 ≤ y by linarith, show 0 ≤ z by linarith, h]
      have h3 : y = 0 := by nlinarith [show 0 ≤ x by linarith, show 0 ≤ y by linarith, show 0 ≤ z by linarith, h]
      have h4 : z = 0 := by nlinarith [show 0 ≤ x by linarith, show 0 ≤ y by linarith, show 0 ≤ z by linarith, h]
      have h5 : x = 0 ∧ y = 0 ∧ z = 0 := ⟨h2, h3, h4⟩
      contradiction
    have h2 : (sqrt (x ^ 2 + y ^ 2 + x * y) + sqrt (y ^ 2 + z ^ 2 + y * z) + sqrt (z ^ 2 + x ^ 2 + z * x)) / (x + y + z) ≥ Real.sqrt 3 := by
      have h3 : sqrt (x^2 + y^2 + x * y) + sqrt (y^2 + z^2 + y * z) + sqrt (z^2 + x^2 + z * x) ≥ Real.sqrt 3 * (x + y + z) := by
        have h4 : sqrt (x ^ 2 + y ^ 2 + x * y) ≥ Real.sqrt 3 / 2 * (x + y) := by 
          have h5 : (x ^ 2 + y ^ 2 + x * y : ℝ) ≥ (3 / 4) * (x + y) ^ 2 := by 
            nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
          have h7 : sqrt (x ^ 2 + y ^ 2 + x * y) ≥ sqrt ((3 / 4) * (x + y) ^ 2) := Real.sqrt_le_sqrt (by linarith)
          have h8 : sqrt ((3 / 4) * (x + y) ^ 2) = Real.sqrt (3 / 4) * Real.sqrt ((x + y) ^ 2) := by 
            rw [Real.sqrt_mul (by positivity)]
          have h9 : Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
            <;> ring_nf <;> norm_num 
          have h10 : Real.sqrt ((x + y) ^ 2) = x + y := by 
            rw [Real.sqrt_sq (by linarith)]
          rw [h8, h9, h10] at h7 
          linarith 
        have h5 : sqrt (y ^ 2 + z ^ 2 + y * z) ≥ Real.sqrt 3 / 2 * (y + z) := by 
          have h6 : (y ^ 2 + z ^ 2 + y * z : ℝ) ≥ (3 / 4) * (y + z) ^ 2 := by 
            nlinarith [sq_nonneg (y - z), sq_nonneg (y + z)]
          have h7 : sqrt (y ^ 2 + z ^ 2 + y * z) ≥ sqrt ((3 / 4) * (y + z) ^ 2) := Real.sqrt_le_sqrt (by linarith)
          have h8 : sqrt ((3 / 4) * (y + z) ^ 2) = Real.sqrt (3 / 4) * Real.sqrt ((y + z) ^ 2) := by 
            rw [Real.sqrt_mul (by positivity)]
          have h9 : Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
            <;> ring_nf <;> norm_num 
          have h10 : Real.sqrt ((y + z) ^ 2) = y + z := by 
            rw [Real.sqrt_sq (by linarith)]
          rw [h8, h9, h10] at h7 
          linarith 
        have h6 : sqrt (z ^ 2 + x ^ 2 + z * x) ≥ Real.sqrt 3 / 2 * (z + x) := by 
          have h7 : (z ^ 2 + x ^ 2 + z * x : ℝ) ≥ (3 / 4) * (z + x) ^ 2 := by 
            nlinarith [sq_nonneg (z - x), sq_nonneg (z + x)]
          have h8 : sqrt (z ^ 2 + x ^ 2 + z * x) ≥ sqrt ((3 / 4) * (z + x) ^ 2) := Real.sqrt_le_sqrt (by linarith)
          have h9 : sqrt ((3 / 4) * (z + x) ^ 2) = Real.sqrt (3 / 4) * Real.sqrt ((z + x) ^ 2) := by 
            rw [Real.sqrt_mul (by positivity)]
          have h10 : Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
            <;> ring_nf <;> norm_num 
          have h11 : Real.sqrt ((z + x) ^ 2) = z + x := by 
            rw [Real.sqrt_sq (by linarith)]
          rw [h9, h10, h11] at h8 
          linarith 
        linarith [h4, h5, h6]
      apply (le_div_iff₀ (by linarith)).mpr
      linarith [h3]
    linarith [heq, h2]