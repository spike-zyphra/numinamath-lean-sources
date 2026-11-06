import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_190622 (z : ℂ) (h : 2 * abs (z - 3 - 3 * .I) = abs z) :
    abs z ≤ 6 * Real.sqrt 2 ∧ abs z ≥ 2 * Real.sqrt 2 := by
  have h1 : 4 * ((z.re - 3) ^ 2 + (z.im - 3) ^ 2) = z.re ^ 2 + z.im ^ 2 := by 
    have eq1 : abs (z - 3 - 3 * Complex.I) = Real.sqrt ((z.re - 3) ^ 2 + (z.im - 3) ^ 2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    have eq2 : abs z = Real.sqrt (z.re^2 + z.im^2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [eq1, eq2] at h
    have h2 : 2 * Real.sqrt ((z.re - 3) ^ 2 + (z.im - 3) ^ 2) = Real.sqrt (z.re^2 + z.im^2) := h
    have h3 : (2 * Real.sqrt ((z.re - 3) ^ 2 + (z.im - 3) ^ 2)) ^ 2 = (Real.sqrt (z.re^2 + z.im^2)) ^ 2 := by 
      rw [h2]
    have h4 : 4 * ((z.re - 3) ^ 2 + (z.im - 3) ^ 2) = z.re^2 + z.im^2 := by
      have h5 : (2 * Real.sqrt ((z.re - 3) ^ 2 + (z.im - 3) ^ 2)) ^ 2 = 4 * ((z.re - 3) ^ 2 + (z.im - 3) ^ 2) := by
        calc
          (2 * Real.sqrt ((z.re - 3) ^ 2 + (z.im - 3) ^ 2)) ^ 2
            = 4 * (Real.sqrt ((z.re - 3) ^ 2 + (z.im - 3) ^ 2)) ^ 2 := by ring_nf
          _ = 4 * ((z.re - 3) ^ 2 + (z.im - 3) ^ 2) := by
            rw [Real.sq_sqrt (by positivity)]
      have h6 : (Real.sqrt (z.re^2 + z.im^2)) ^ 2 = z.re^2 + z.im^2 := Real.sq_sqrt (by positivity)
      nlinarith [h5, h6, h3]
    exact h4
  have h8 : (z.re - 4) ^ 2 + (z.im - 4) ^ 2 = 8 := by
    nlinarith [h1]
  have h10 : z.re^2 + z.im^2 ≤ 72 := by
    nlinarith [sq_nonneg (z.re - 4), sq_nonneg (z.im - 4), sq_nonneg ((z.re - 4) - (z.im - 4)), sq_nonneg ((z.re - 4) + (z.im - 4)), sq_nonneg (z.re), sq_nonneg (z.im)]
  have h11 : z.re^2 + z.im^2 ≥ 8 := by
    nlinarith [sq_nonneg (z.re - 4), sq_nonneg (z.im - 4), sq_nonneg ((z.re - 4) - (z.im - 4)), sq_nonneg ((z.re - 4) + (z.im - 4)), sq_nonneg (z.re), sq_nonneg (z.im)]
  have h12 : abs z ≤ 6 * Real.sqrt 2 := by
    have h13 : abs z = Real.sqrt (z.re^2 + z.im^2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h13]
    have h14 : Real.sqrt (z.re^2 + z.im^2) ≤ Real.sqrt (72 : ℝ) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    have h15 : Real.sqrt (72 : ℝ) = 6 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    linarith [h14, h15]
  have h16 : abs z ≥ 2 * Real.sqrt 2 := by
    have h13 : abs z = Real.sqrt (z.re^2 + z.im^2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h13]
    have h18 : Real.sqrt (z.re^2 + z.im^2) ≥ Real.sqrt (8 : ℝ) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    have h19 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    linarith [h18, h19]
  exact ⟨h12, h16⟩