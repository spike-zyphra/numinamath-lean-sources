import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_13380 :
  IsLeast {x : ℝ | ∃ z : ℂ, x = abs (z - 1 + 2 * I) ^ 2 + abs (z - 9 - 4 * I) ^ 2 ∧ abs (z - 5 - I) = 5} 100 := by
  constructor
  · -- Show 100 is in the set.
    use 5 + 6 * I
    constructor
    · -- Show x = |z - 1 + 2i|^2 + |z - 9 - 4i|^2
      have h1 : abs ((5 + 6 * I : ℂ) - 1 + 2 * I) = Real.sqrt 80 := by
        simp [Complex.abs, Complex.normSq]
        ring_nf
      have h2 : abs ((5 + 6 * I : ℂ) - 9 - 4 * I) = Real.sqrt 20 := by
        simp [Complex.abs, Complex.normSq]
        ring_nf
      rw [h1, h2]
      have h3 : (Real.sqrt 80 : ℝ) ^ 2 = 80 := Real.sq_sqrt (by norm_num)
      have h4 : (Real.sqrt 20 : ℝ) ^ 2 = 20 := Real.sq_sqrt (by norm_num)
      nlinarith [h3, h4]
    · -- Show |z - 5 - I| = 5
      simp [Complex.abs, Complex.normSq]
      ring_nf
  · -- Show 100 is the minimum.
    intro x hx
    rcases hx with ⟨z, hx1, hx2⟩
    have h1 : abs (z - 1 + 2 * I) ^ 2 + abs (z - 9 - 4 * I) ^ 2 ≥ 100 := by
      have h3 : abs (z - 1 + 2 * I) ^ 2 = (z.re - 1) ^ 2 + (z.im + 2) ^ 2 := by
        have h1 : abs (z - 1 + 2 * I) = Real.sqrt ((z.re - 1) ^ 2 + (z.im + 2) ^ 2) := by
          simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
          <;> ring_nf
        rw [h1]
        rw [Real.sq_sqrt (by positivity)]
      have h4 : abs (z - 9 - 4 * I) ^ 2 = (z.re - 9) ^ 2 + (z.im - 4) ^ 2 := by
        have h1 : abs (z - 9 - 4 * I) = Real.sqrt ((z.re - 9) ^ 2 + (z.im - 4) ^ 2) := by
          simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
          <;> ring_nf
        rw [h1]
        rw [Real.sq_sqrt (by positivity)]
      have h5 : (z.re - 5) ^ 2 + (z.im - 1) ^ 2 = 25 := by
        have h6 : abs (z - 5 - I) = 5 := hx2
        have h7 : abs (z - 5 - I) = Real.sqrt ((z.re - 5) ^ 2 + (z.im - 1) ^ 2) := by
          simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
          <;> ring_nf
        rw [h7] at h6
        have h8 : (Real.sqrt ((z.re - 5) ^ 2 + (z.im - 1) ^ 2) : ℝ) = 5 := h6
        have h9 : (z.re - 5) ^ 2 + (z.im - 1) ^ 2 ≥ 0 := by positivity
        have h10 : (Real.sqrt ((z.re - 5) ^ 2 + (z.im - 1) ^ 2)) ^ 2 = (z.re - 5) ^ 2 + (z.im - 1) ^ 2 := Real.sq_sqrt (by positivity)
        nlinarith [h8, h10]
      have h11 : (z.re - 1) ^ 2 + (z.im + 2) ^ 2 + (z.re - 9) ^ 2 + (z.im - 4) ^ 2 ≥ 100 := by
        nlinarith [sq_nonneg (z.re - 5), sq_nonneg (z.im - 1), 
          sq_nonneg ((z.re - 5) - 0), sq_nonneg ((z.im - 1) - 6), 
          sq_nonneg ((z.re - 5) - 0), sq_nonneg ((z.im - 1) + 4), 
          h5]
      linarith [h3, h4, h11]
    linarith [hx1, h1]