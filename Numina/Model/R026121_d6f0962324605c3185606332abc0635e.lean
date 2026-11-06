import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_135954 {z : ℂ} (hz : ∃ r : ℝ, (z - I) / (z - 1) = r * I) :
    abs z ≤ Real.sqrt 2 := by
  rcases hz with ⟨r, hr⟩
  by_cases h11 : z - 1 = 0
  · -- Case where z = 1
    have h2 : z = 1 := by
      have h' : z - 1 = 0 := h11
      have : z = 1 := by
        calc
          z = (z - 1) + 1 := by ring_nf
          _ = 0 + 1 := by rw [h']
          _ = 1 := by ring_nf
      assumption
    rw [h2]
    simp [Complex.abs, Complex.normSq]
    all_goals
      try { norm_num [Real.sqrt_le_sqrt] }
      <;> linarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Case where z ≠ 1
    have h111 : z - 1 ≠ 0 := h11
    have h3 : z.re^2 - z.re + z.im^2 - z.im = 0 := by
      have h4 : z - 1 ≠ 0 := h111
      have eq3 : (z - I) / (z - 1) = r * I := hr
      have eq4 : (z - I) = (r * I) * (z - 1) := by 
        field_simp [h4] at eq3 ⊢
        simpa using eq3
      have eq5 := congr_arg Complex.re eq4
      have eq6 := congr_arg Complex.im eq4
      simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at eq5 eq6 
      ring_nf at eq5 eq6 
      by_cases h8 : z.im = 0
      · 
        rw [h8] at eq5 eq6 
        have hr0 : z.re = 0 := by nlinarith 
        nlinarith 
      · -- Case where z.im ≠ 0 
        have h9 : r = - z.re / z.im := by 
          field_simp [h8] 
          nlinarith [eq5] 
        rw [h9] at eq6 
        field_simp [h8] at eq6 
        ring_nf at eq6 
        nlinarith 
    have h5 : z.re^2 + z.im^2 ≤ 2 := by
      nlinarith [sq_nonneg (z.re - 1 / 2), sq_nonneg (z.im - 1 / 2), 
                  h3, sq_nonneg (z.re - z.im)]
    have h3 : abs z = Real.sqrt (z.re^2 + z.im^2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring
    rw [h3]
    have h6 : Real.sqrt (z.re^2 + z.im^2) ≤ Real.sqrt (2 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith [h5]
    linarith [Real.sqrt_nonneg (2 : ℝ), h6]