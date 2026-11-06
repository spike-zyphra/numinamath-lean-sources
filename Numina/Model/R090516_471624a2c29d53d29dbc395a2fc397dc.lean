import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_190700 {m : ℝ} (z : ℂ) (hz : z = 1 + I + m / (1 + I)) :
    (z.re > 0 ∧ z.im > 0) ↔ m ∈ Set.Ioo (-2) 2 := by
  constructor
  · -- Assume (z.re > 0 ∧ z.im > 0), prove (m ∈ Set.Ioo (-2) 2)
    intro h
    rcases h with ⟨h₁, h₂⟩
    have h_eq1 : z.re = 1 + m / 2 := by
      rw [hz]
      simp [Complex.div_re, Complex.normSq, Complex.ofReal_re, Complex.I_re, Complex.I_im]
      <;> ring_nf <;> norm_num
      <;> field_simp
      <;> ring
    have h_eq2 : z.im = 1 - m / 2 := by
      rw [hz]
      simp [Complex.div_im, Complex.normSq, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      <;> ring_nf <;> norm_num
      <;> field_simp
      <;> ring
    rw [h_eq1] at h₁
    rw [h_eq2] at h₂
    constructor
    · -- Prove $-2 < m$
      linarith
    · -- Prove $m < 2$
      linarith
  · -- Assume (m ∈ Set.Ioo (-2) 2), prove (z.re > 0 ∧ z.im > 0)
    rintro ⟨h₁, h₂⟩
    have h_eq1 : z.re = 1 + m / 2 := by
      rw [hz]
      simp [Complex.div_re, Complex.normSq, Complex.ofReal_re, Complex.I_re, Complex.I_im]
      <;> ring_nf <;> norm_num
      <;> field_simp
      <;> ring
    have h_eq2 : z.im = 1 - m / 2 := by
      rw [hz]
      simp [Complex.div_im, Complex.normSq, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      <;> ring_nf <;> norm_num
      <;> field_simp
      <;> ring
    constructor
    · -- Prove z.re > 0
      rw [h_eq1]
      linarith
    · -- Prove z.im > 0
      rw [h_eq2]
      linarith