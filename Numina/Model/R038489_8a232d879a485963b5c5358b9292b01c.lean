import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_13787 : IsLeast {abs z | (z : ℂ) (h : abs (z - 3 * .I) + abs (z - 4) = 5)} (12 / 5) := by
  constructor
  · -- Show 12/5 is in the set
    use (36 / 25 + Complex.I * (48 / 25))
    constructor
    · -- Show |z| = 12/5
      have h1 : abs ((36 / 25 + Complex.I * (48 / 25)) : ℂ) = 12 / 5 := by
        simp [Complex.abs, Complex.normSq]
        ring_nf
        have h2 : Real.sqrt (144 / 25) = 12 / 5 := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        rw [h2]
      linarith
    · -- Show |z - 3i| + |z - 4| = 5
      have h2 : abs ((36 / 25 + Complex.I * (48 / 25) - 3 * Complex.I) : ℂ) + abs ((36 / 25 + Complex.I * (48 / 25) - 4) : ℂ) = 5 := by
        have h3 : abs ((36 / 25 + Complex.I * (48 / 25) - 3 * Complex.I) : ℂ) = 9 / 5 := by
          have h36 : (36 / 25 + Complex.I * (48 / 25) - 3 * Complex.I : ℂ) = (36 / 25 : ℝ) + Complex.I * ((48 / 25 - 75 / 25) : ℝ) := by 
            simp [Complex.ext_iff, mul_add, mul_assoc]
            all_goals ring_nf
          rw [h36]
          simp [Complex.abs, Complex.normSq]
          ring_nf
          have h2 : Real.sqrt (81 / 25) = 9 / 5 := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h2]
        have h4 : abs ((36 / 25 + Complex.I * (48 / 25) - 4) : ℂ) = 16 / 5 := by
          have h36 : (36 / 25 + Complex.I * (48 / 25) - 4 : ℂ) = ((36 / 25 - 100 / 25) : ℝ) + Complex.I * (48 / 25 : ℝ) := by
            simp [Complex.ext_iff, mul_add, mul_assoc]
            all_goals ring_nf
          rw [h36]
          simp [Complex.abs, Complex.normSq]
          ring_nf
          have h2 : Real.sqrt (256 / 25) = 16 / 5 := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h2]
        linarith [h3, h4]
      linarith
  · -- Show 12/5 is the least
    intro r hr
    rcases hr with ⟨z, h_eq, h_abs⟩
    have h1 : abs (z - 3 * Complex.I) + abs (z - 4) = 5 := h_eq
    have h2 : abs (z) ≥ 12 / 5 := by
      have h3 : abs (z - 3 * Complex.I) = Real.sqrt (z.re ^ 2 + (z.im - 3) ^ 2) := by
        simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
        all_goals
          ring_nf
      have h4' : abs (z - 4) = Real.sqrt ((z.re - 4) ^ 2 + z.im ^ 2) := by
        simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
        all_goals
          ring_nf
      rw [h3, h4'] at h1
      have h36 : Real.sqrt (z.re ^ 2 + (z.im - 3) ^ 2) + Real.sqrt ((z.re - 4) ^ 2 + z.im ^ 2) = 5 := by
        nlinarith
      have h11 : (3 * z.re + 4 * z.im) = 12 := by
        have h31 : Real.sqrt (z.re ^ 2 + (z.im - 3) ^ 2) + Real.sqrt ((z.re - 4) ^ 2 + z.im ^ 2) = 5 := by
          nlinarith
        have h31 : Real.sqrt (z.re ^ 2 + (z.im - 3) ^ 2) + Real.sqrt ((z.re - 4) ^ 2 + z.im ^ 2) = 5 := by
          nlinarith
        have h36 : Real.sqrt (z.re ^ 2 + (z.im - 3) ^ 2) ^ 2 + Real.sqrt ((z.re - 4) ^ 2 + z.im ^ 2) ^ 2 + 2 * (Real.sqrt (z.re ^ 2 + (z.im - 3) ^ 2) * Real.sqrt ((z.re - 4) ^ 2 + z.im ^ 2)) = 25 := by
          have h34 : Real.sqrt (z.re ^ 2 + (z.im - 3) ^ 2) + Real.sqrt ((z.re - 4) ^ 2 + z.im ^ 2) = 5 := by
            nlinarith
          have h35 : (Real.sqrt (z.re ^ 2 + (z.im - 3) ^ 2) + Real.sqrt ((z.re - 4) ^ 2 + z.im ^ 2)) ^ 2 = 25 := by
            rw [h34]
            norm_num
          nlinarith
        have h36' : Real.sqrt (z.re ^ 2 + (z.im - 3) ^ 2) ^ 2 = z.re ^ 2 + (z.im - 3) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        have h37' : Real.sqrt ((z.re - 4) ^ 2 + z.im ^ 2) ^ 2 = (z.re - 4) ^ 2 + z.im ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        rw [h36', h37'] at h36
        nlinarith [sq_nonneg (z.re - 36 / 25), sq_nonneg (z.im - 48 / 25), Real.sqrt_nonneg (z.re ^ 2 + (z.im - 3) ^ 2), Real.sqrt_nonneg ((z.re - 4) ^ 2 + z.im ^ 2), mul_nonneg (Real.sqrt_nonneg (z.re ^ 2 + (z.im - 3) ^ 2)) (Real.sqrt_nonneg ((z.re - 4) ^ 2 + z.im ^ 2)), mul_nonneg (show (0 : ℝ) ≤ z.re ^ 2 + (z.im - 3) ^ 2 by positivity) (show (0 : ℝ) ≤ (z.re - 4) ^ 2 + z.im ^ 2 by positivity)]
      have h13 : abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
        simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
        all_goals
          ring_nf
      have h14 : abs z ≥ 12 / 5 := by
        have h36 : z.re ^ 2 + z.im ^ 2 ≥ 144 / 25 := by
          nlinarith [sq_nonneg (3 * z.re - 4 * z.im), sq_nonneg (4 * z.re - 3 * z.im), sq_nonneg (z.re - 36 / 25), sq_nonneg (z.im - 48 / 25), sq_nonneg (3 * z.re + 4 * z.im - 12)]
        have h31 : abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
          simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
          all_goals
            ring_nf
        rw [h31]
        have h34 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≥ Real.sqrt (144 / 25 : ℝ) := by
          apply Real.sqrt_le_sqrt
          linarith [h36]
        have h35 : Real.sqrt (144 / 25 : ℝ) = (12 / 5 : ℝ) := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        linarith
      linarith
    linarith [h2, h_abs]