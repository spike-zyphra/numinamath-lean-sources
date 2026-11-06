import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_189130
  (z1 z2 z3 : ℂ)
  (h₁ : ‖z1‖ = Real.sqrt 2)
  (h₂ : ‖z2‖ = Real.sqrt 2)
  (h₃ : z1.re * z2.re + z1.im * z2.im = 0)
  (h₄ : ‖z1 + z2 - z3‖ = 1) :
  1 ≤ ‖z3‖ ∧ ‖z3‖ ≤ 3 := by

  have h7 : z1.re ^ 2 + z1.im ^ 2 = 2 := by
    have h8 : ‖z1‖ = Real.sqrt 2 := h₁
    have h8' : ‖z1‖ = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h8'] at h8
    have h9 : z1.re ^ 2 + z1.im ^ 2 = (2 : ℝ) := by
      calc
        z1.re ^ 2 + z1.im ^ 2 = (Real.sqrt (z1.re ^ 2 + z1.im ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (Real.sqrt 2) ^ 2 := by
          rw [h8]
        _ = (2 : ℝ) := by
          norm_num
    linarith

  have h8' : z2.re ^ 2 + z2.im ^ 2 = 2 := by
    have h9 : ‖z2‖ = Real.sqrt 2 := h₂
    have h9' : ‖z2‖ = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h9'] at h9
    have h10 : z2.re ^ 2 + z2.im ^ 2 = (2 : ℝ) := by
      calc
        z2.re ^ 2 + z2.im ^ 2 = (Real.sqrt (z2.re ^ 2 + z2.im ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (Real.sqrt 2) ^ 2 := by
          rw [h9]
        _ = (2 : ℝ) := by
          norm_num
    linarith

  have h11 : ‖z1 + z2‖ = 2 := by
    have h12 : ‖z1 + z2‖ = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h12]
    have h13 : (z1.re + z2.re : ℝ) ^ 2 + (z1.im + z2.im : ℝ) ^ 2 = (4 : ℝ) := by
      nlinarith [h₃, h7, h8']
    rw [h13]
    have h14 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact_mod_cast h14

  have h13 : ‖z3‖ ≤ 3 := by
    have h16 : ‖z3‖ ≤ ‖z1 + z2‖ + ‖z1 + z2 - z3‖ := by
      have h17 : ‖z3‖ = ‖(z1 + z2) - (z1 + z2 - z3)‖ := by
        simp [Complex.ext_iff]
        <;> ring_nf
      rw [h17]
      apply norm_sub_le
    rw [h11] at h16
    have h14 : ‖z1 + z2 - z3‖ = 1 := h₄
    linarith [h14, h16]

  have h14 : 1 ≤ ‖z3‖ := by
    have h16 : ‖z1 + z2 - z3‖ ≥ ‖z1 + z2‖ - ‖z3‖ := by
      apply norm_sub_norm_le
    have h17 : ‖z1 + z2 - z3‖ = 1 := h₄
    have h11' : ‖z1 + z2‖ = 2 := h11
    linarith [h17, h11', h16]

  constructor
  · -- Show 1 ≤ ‖z3‖
    linarith [h14]
  · -- Show ‖z3‖ ≤ 3
    linarith [h13]