import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_20858 :
  IsLeast {z : ℝ | ∃ x y : ℝ, x ∈ Icc 0 40 ∧ y ∈ Icc 0 50 ∧
    z = sqrt (x^2 + 400) + sqrt (y^2 + 900) +
      sqrt (x^2 + y^2 - 80 * x - 100 * y + 4100)} (70 * sqrt 2) := by
  constructor 
  · -- Prove that 70 * sqrt 2 is in the set
    use 20
    use 30
    constructor
    · norm_num [mem_Icc]
    constructor
    · norm_num [mem_Icc]
    · -- Show that the sum equals 70 * sqrt 2
      have h1 : sqrt (20^2 + 400) = 20 * sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h2 : sqrt (30^2 + 900) = 30 * sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h3 : sqrt (20^2 + 30^2 - 80 * 20 - 100 * 30 + 4100) = 20 * sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h1, h2, h3]
      ring
  · -- Prove that 70 * sqrt 2 is the least elements
    intro z hz
    rcases hz with ⟨x, y, hx, hy, hz⟩
    rcases hx with ⟨hx₀, hx₁⟩
    rcases hy with ⟨hy₀, hy₁⟩
    have h1 : sqrt (x^2 + 400) ≥ (x + 20) / Real.sqrt 2 := by
      have h : sqrt (x^2 + 400) ≥ (x + 20) / Real.sqrt 2 := by
        have h1 : Real.sqrt (x^2 + 400) ^ 2 ≥ ((x + 20) / Real.sqrt 2) ^ 2 := by
          have : Real.sqrt (x^2 + 400) ^ 2 = x^2 + 400 := by
            rw [Real.sq_sqrt]
            positivity
          rw [this]
          have : ((x + 20) / Real.sqrt 2) ^ 2 = (x + 20)^2 / (Real.sqrt 2 ^ 2) := by
            ring_nf
          rw [this]
          have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          rw [h2]
          nlinarith [sq_nonneg (x - 20)]
        nlinarith [Real.sqrt_nonneg (x^2 + 400), show 0 ≤ (x + 20) / Real.sqrt 2 by 
          apply div_nonneg 
          · linarith 
          · positivity
         ]
      linarith
    have h2 : sqrt (y^2 + 900) ≥ (y + 30) / Real.sqrt 2 := by
      have h : sqrt (y^2 + 900) ≥ (y + 30) / Real.sqrt 2 := by
        have h1 : Real.sqrt (y^2 + 900) ^ 2 ≥ ((y + 30) / Real.sqrt 2) ^ 2 := by
          have : Real.sqrt (y^2 + 900) ^ 2 = y^2 + 900 := by
            rw [Real.sq_sqrt]
            positivity
          rw [this]
          have : ((y + 30) / Real.sqrt 2) ^ 2 = (y + 30)^2 / (Real.sqrt 2 ^ 2) := by
            ring_nf
          rw [this]
          have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          rw [h2]
          nlinarith [sq_nonneg (y - 30)]
        nlinarith [Real.sqrt_nonneg (y^2 + 900), show 0 ≤ (y + 30) / Real.sqrt 2 by 
          apply div_nonneg 
          · linarith 
          · positivity
         ]
      linarith
    have h3 : sqrt (x^2 + y^2 - 80 * x - 100 * y + 4100) ≥ ( (40 - x) + (50 - y) ) / Real.sqrt 2 := by
      have h_eq : x^2 + y^2 - 80 * x - 100 * y + 4100 = (x - 40)^2 + (y - 50)^2 := by ring
      rw [h_eq]
      have h : Real.sqrt ((x - 40)^2 + (y - 50)^2) ≥ ( (40 - x) + (50 - y) ) / Real.sqrt 2 := by
        have h1 : Real.sqrt ((x - 40)^2 + (y - 50)^2) ^ 2 ≥ ( ( (40 - x) + (50 - y) ) / Real.sqrt 2 )^2 := by
          have : Real.sqrt ((x - 40)^2 + (y - 50)^2) ^ 2 = (x - 40)^2 + (y - 50)^2 := by
            rw [Real.sq_sqrt]
            positivity
          rw [this]
          have : ( ( (40 - x) + (50 - y) ) / Real.sqrt 2 )^2 = ( (40 - x) + (50 - y) )^2 / (Real.sqrt 2 ^ 2) := by
            ring_nf
          rw [this]
          have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          rw [h2]
          nlinarith [sq_nonneg ( (x - 40) - (50 - y) ), sq_nonneg ( (y - 50) + (40 - x) ) ]
        nlinarith [Real.sqrt_nonneg ((x - 40)^2 + (y - 50)^2), show 0 ≤ ( (40 - x) + (50 - y) ) / Real.sqrt 2 by 
          apply div_nonneg 
          · nlinarith
          · positivity
         ]
      linarith
    have h4 : sqrt (x^2 + 400) + sqrt (y^2 + 900) + sqrt (x^2 + y^2 - 80 * x - 100 * y + 4100) ≥ 
      (x + 20) / Real.sqrt 2 + (y + 30) / Real.sqrt 2 + ( (40 - x) + (50 - y) ) / Real.sqrt 2 := by 
      linarith [h1, h2, h3]
    have h5 : (x + 20) / Real.sqrt 2 + (y + 30) / Real.sqrt 2 + ( (40 - x) + (50 - y) ) / Real.sqrt 2 = 70 * Real.sqrt 2 := by
      field_simp
      ring_nf
      <;> norm_num [Real.sq_sqrt]
      <;> linarith
    nlinarith [h4, h5, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0)]