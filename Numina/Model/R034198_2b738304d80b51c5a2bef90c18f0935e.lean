import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_21782 :
  IsLeast {x : ℝ | ∃ z : ℂ, x = abs (z - 3)^2 + abs (z - 5 + 2 * I)^2 + abs (z - 1 + I)^2} 10 := by
  constructor
  · -- Show 10 is in the set
    use (3 - Complex.I)
    simp [Complex.abs, Complex.normSq, Complex.normSq]
    <;> norm_num [Complex.ext_iff, pow_two, Complex.normSq]
  · -- Show 10 is the least element
    intro x hx
    rcases hx with ⟨z, h⟩
    have h1 : abs (z - 3) ^ 2 = (z.re - 3) ^ 2 + z.im ^ 2 := by
      have h2 : abs (z - 3) = Real.sqrt ((z.re - 3) ^ 2 + z.im ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring_nf
      rw [h2]
      rw [Real.sq_sqrt (by positivity)]
    have h2 : abs (z - 5 + 2 * I) ^ 2 = (z.re - 5) ^ 2 + (z.im + 2) ^ 2 := by
      have h3 : abs (z - 5 + 2 * I) = Real.sqrt ((z.re - 5) ^ 2 + (z.im + 2) ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring_nf
      rw [h3]
      rw [Real.sq_sqrt (by positivity)]
    have h3 : abs (z - 1 + I) ^ 2 = (z.re - 1) ^ 2 + (z.im + 1) ^ 2 := by
      have h4 : abs (z - 1 + I) = Real.sqrt ((z.re - 1) ^ 2 + (z.im + 1) ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring_nf
      rw [h4]
      rw [Real.sq_sqrt (by positivity)]
    rw [h1, h2, h3] at h
    nlinarith [sq_nonneg (z.re - 3), sq_nonneg (z.im + 1)]