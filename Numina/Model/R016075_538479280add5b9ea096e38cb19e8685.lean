import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_198628 {z1 z2 : ℂ} (hz1 : abs z1 = 2) (hz2 : abs z2 = 3)
  (h : ∃ θ, θ = π / 3 ∧ z1.re * z2.re + z1.im * z2.im = abs z1 * abs z2 * Real.cos θ) :
  abs (z1 + z2) / abs (z1 - z2) = Real.sqrt 133 / 7 := by

  rcases h with ⟨θ, hθ, h⟩
  have h1 : θ = π / 3 := hθ
  have h4 : abs z1 = 2 := hz1
  have h5 : abs z2 = 3 := hz2
  have h3 : z1.re * z2.re + z1.im * z2.im = abs z1 * abs z2 * (1 / 2) := by
    rw [h1] at h
    have h4 : Real.cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
    rw [h4] at h
    linarith
  have h6 : abs (z1 + z2) = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by
    have h11 : abs (z1 + z2) = Real.sqrt ((z1 + z2).re ^ 2 + (z1 + z2).im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring
    have h12 : (z1 + z2).re = z1.re + z2.re := by simp
    have h13 : (z1 + z2).im = z1.im + z2.im := by simp
    rw [h12, h13] at h11
    linarith
  have h7 : abs (z1 - z2) = Real.sqrt ((z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2) := by
    have h11 : abs (z1 - z2) = Real.sqrt ((z1 - z2).re ^ 2 + (z1 - z2).im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring
    have h12 : (z1 - z2).re = z1.re - z2.re := by simp
    have h13 : (z1 - z2).im = z1.im - z2.im := by simp
    rw [h12, h13] at h11
    linarith
  have h8 : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 = 19 := by
    have h9 : z1.re ^ 2 + z1.im ^ 2 = 4 := by
      have h11 : abs z1 = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring
      rw [h11] at h4
      have h12 : Real.sqrt (z1.re ^ 2 + z1.im ^ 2) = 2 := h4
      have h13 : z1.re ^ 2 + z1.im ^ 2 = 4 := by
        calc
          z1.re ^ 2 + z1.im ^ 2 = (Real.sqrt (z1.re ^ 2 + z1.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = 2 ^ 2 := by rw [h12]
          _ = 4 := by norm_num
      linarith
    have h10 : z2.re ^ 2 + z2.im ^ 2 = 9 := by
      have h11 : abs z2 = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring
      rw [h11] at h5
      have h12 : Real.sqrt (z2.re ^ 2 + z2.im ^ 2) = 3 := h5
      have h13 : z2.re ^ 2 + z2.im ^ 2 = 9 := by
        calc
          z2.re ^ 2 + z2.im ^ 2 = (Real.sqrt (z2.re ^ 2 + z2.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = 3 ^ 2 := by rw [h12]
          _ = 9 := by norm_num
      linarith
    have h11 : z1.re * z2.re + z1.im * z2.im = 3 := by
      rw [h4, h5] at h3
      norm_num at h3 ⊢
      linarith
    nlinarith [h9, h10, h11]
  have h9 : (z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2 = 7 := by
    have h9 : z1.re ^ 2 + z1.im ^ 2 = 4 := by
      have h11 : abs z1 = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring
      rw [h11] at h4
      have h12 : Real.sqrt (z1.re ^ 2 + z1.im ^ 2) = 2 := h4
      have h13 : z1.re ^ 2 + z1.im ^ 2 = 4 := by
        calc
          z1.re ^ 2 + z1.im ^ 2 = (Real.sqrt (z1.re ^ 2 + z1.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = 2 ^ 2 := by rw [h12]
          _ = 4 := by norm_num
      linarith
    have h10 : z2.re ^ 2 + z2.im ^ 2 = 9 := by
      have h11 : abs z2 = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring
      rw [h11] at h5
      have h12 : Real.sqrt (z2.re ^ 2 + z2.im ^ 2) = 3 := h5
      have h13 : z2.re ^ 2 + z2.im ^ 2 = 9 := by
        calc
          z2.re ^ 2 + z2.im ^ 2 = (Real.sqrt (z2.re ^ 2 + z2.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = 3 ^ 2 := by rw [h12]
          _ = 9 := by norm_num
      linarith
    have h11 : z1.re * z2.re + z1.im * z2.im = 3 := by
      rw [h4, h5] at h3
      norm_num at h3 ⊢
      linarith
    nlinarith [h9, h10, h11]
  have h10 : abs (z1 + z2) = Real.sqrt 19 := by
    rw [h6]
    rw [h8]
  have h11 : abs (z1 - z2) = Real.sqrt 7 := by
    rw [h7]
    rw [h9]
  rw [h10, h11]
  have h13 : Real.sqrt 19 / Real.sqrt 7 = Real.sqrt (19 / (7 : ℝ)) := by
    field_simp [Real.sqrt_div]
  have h14 : Real.sqrt (19 / (7 : ℝ)) = Real.sqrt 133 / 7 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h13, h14]
  <;> ring