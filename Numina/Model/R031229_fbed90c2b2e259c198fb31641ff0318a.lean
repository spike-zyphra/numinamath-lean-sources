import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_217970 (z : ℂ) (hz : abs ((z - I) / (z - 3 * I)) = 1 / 2) :
    abs z ≤ abs (5 / 3 * I) := by

  have h1 : abs ((z - I) / (z - 3 * I)) = abs (z - I) / abs (z - 3 * I) := by
    simp [abs_div]

  have h2 : abs (z - I) / abs (z - 3 * I) = 1 / 2 := by
    rw [h1] at hz 
    exact_mod_cast hz

  have h3 : abs (z - I) = (1 / 2) * abs (z - 3 * I) := by
    have h4 : abs (z - 3 * I) ≠ 0 := by
      by_contra h
      have h2' : abs (z - I) / abs (z - 3 * I) = 1 / 2 := h2
      rw [h] at h2' 
      norm_num at h2' 
      all_goals try { nlinarith }
      all_goals try { tauto }
    have h5 : abs (z - I) = (1 / 2) * abs (z - 3 * I) := by
      have h2' : abs (z - I) / abs (z - 3 * I) = 1 / 2 := h2
      field_simp [h4] at h2' ⊢
      all_goals try { nlinarith }
      all_goals try { tauto }
    exact h5

  have eq1 : abs (z - I) = Real.sqrt ((z.re : ℝ) ^2 + (z.im - 1 : ℝ) ^2) := by
    have h6 : abs (z - I) = Real.sqrt (((z - I).re : ℝ) ^2 + ((z - I).im : ℝ) ^2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [Real.sqrt_sq]
      <;> ring
    rw [h6]
    have h7 : (z - I).re = z.re := by
      simp [Complex.sub_re, Complex.I_re]
    have h8 : (z - I).im = (z.im - 1 : ℝ) := by
      simp [Complex.sub_im, Complex.I_im]
      <;> ring 
    rw [h7, h8]
    all_goals try { ring_nf <;> simp }
    all_goals try { nlinarith }

  have eq2 : abs (z - 3 * I) = Real.sqrt ((z.re : ℝ) ^2 + (z.im - 3 : ℝ) ^2) := by
    have h9 : abs (z - 3 * I) = Real.sqrt (((z - 3 * I).re : ℝ) ^2 + ((z - 3 * I).im : ℝ) ^2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [Real.sqrt_sq]
      <;> ring 
    rw [h9]
    have h10 : (z - 3 * I).re = (z.re : ℝ) := by
      simp [Complex.sub_re, Complex.I_re]
    have h11 : (z - 3 * I).im = (z.im - 3 : ℝ) := by
      simp [Complex.sub_im, Complex.I_im]
      <;> ring
    rw [h10, h11]
    all_goals try { ring_nf <;> simp }
    all_goals try { nlinarith }

  have eq3 : Real.sqrt ((z.re : ℝ) ^2 + (z.im - 1 : ℝ) ^2) = (1 / 2) * Real.sqrt ((z.re : ℝ) ^2 + (z.im - 3 : ℝ) ^2) := by
    rw [eq1] at h3 
    rw [eq2] at h3
    exact_mod_cast h3

  have eq4 : ((z.re : ℝ) ^2 + (z.im - 1 : ℝ) ^2) = (1 / 4) * ((z.re : ℝ) ^2 + (z.im - 3 : ℝ) ^2) := by
    calc
      ((z.re : ℝ) ^2 + (z.im - 1 : ℝ) ^2) = (Real.sqrt ((z.re : ℝ) ^2 + (z.im - 1 : ℝ) ^2)) ^2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = ((1 / 2) * Real.sqrt ((z.re : ℝ) ^2 + (z.im - 3 : ℝ) ^2)) ^2 := by
        rw [eq3]
      _ = (1 / 4) * (Real.sqrt ((z.re : ℝ) ^2 + (z.im - 3 : ℝ) ^2) ^2) := by
        ring_nf 
      _ = (1 / 4) * ((z.re : ℝ) ^2 + (z.im - 3 : ℝ) ^2) := by
        rw [Real.sq_sqrt]
        positivity

  have eq5 : abs z = Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [Real.sqrt_sq]
    <;> ring
  
  have eq6 : abs (5 / 3 * I) = (5 / 3 : ℝ) := by
    simp [Complex.abs, Complex.normSq]
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
    all_goals ring_nf <;> norm_num
    all_goals linarith
  
  rw [eq5, eq6]

  have h7 : Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) ≤ (5 / 3 : ℝ) := by
    have h8 : ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) ≤ (5 / 3 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((z.re : ℝ) ^ 2), sq_nonneg ((z.im : ℝ) ^ 2), sq_nonneg ((z.im - 5/3) ^ 2), sq_nonneg ((z.re)^2 - (z.im ^2)), sq_nonneg ((z.re) ^2 - (z.im - 5/3) ^2)]
    have h9 : (5 / 3 : ℝ) ≥ 0 := by norm_num 
    have h9' : Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) ≤ Real.sqrt ((5 / 3 : ℝ) ^ 2) := by
      apply Real.sqrt_le_sqrt 
      linarith 
    have h10 : Real.sqrt ((5 / 3 : ℝ) ^ 2) = (5 / 3 : ℝ) := by
      rw [Real.sqrt_sq]
      all_goals norm_num
    linarith [h10, h9']
  
  linarith [h7]