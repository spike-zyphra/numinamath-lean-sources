import Mathlib

theorem algebra_180557 {α β : ℝ} (z u : ℂ) (hz : z = Complex.exp (Complex.I * α)) (hu : u = Complex.exp (Complex.I * β))
    (h : z + u = 4 / 5 + 3 / 5 * .I) : Real.tan (α + β) = 24 / 7 := by
  have eq3 := congr_arg Complex.re h
  have eq4 := congr_arg Complex.im h
  rw [hz] at eq3 eq4 
  rw [hu] at eq3 eq4 
  have eq5 : Real.cos α + Real.cos β = 4 / 5 := by 
    simp [Complex.add_re, Complex.exp_re, Complex.ofReal_re, Complex.I_re, Complex.exp_im, Complex.ofReal_im, Complex.I_im] at eq3 eq4 ⊢ 
    ring_nf at eq3 eq4 ⊢ 
    norm_num at eq3 eq4 ⊢ 
    linarith [eq3, eq4]
  have eq6 : Real.sin α + Real.sin β = 3 / 5 := by 
    simp [Complex.add_im, Complex.exp_re, Complex.ofReal_re, Complex.I_re, Complex.exp_im, Complex.ofReal_im, Complex.I_im] at eq3 eq4 ⊢ 
    ring_nf at eq3 eq4 ⊢ 
    norm_num at eq3 eq4 ⊢ 
    linarith [eq3, eq4]
  have h3a : Real.cos α + Real.cos β = 2 * Real.cos ((α + β) / 2) * Real.cos ((α - β) / 2) := by 
    rw [show (α : ℝ) = (α + β) / 2 + (α - β) / 2 by ring]
    rw [show (β : ℝ) = (α + β) / 2 - (α - β) / 2 by ring]
    rw [Real.cos_add, Real.cos_sub]
    ring
  have h3b : Real.sin α + Real.sin β = 2 * Real.sin ((α + β) / 2) * Real.cos ((α - β) / 2) := by 
    rw [show (α : ℝ) = (α + β) / 2 + (α - β) / 2 by ring]
    rw [show (β : ℝ) = (α + β) / 2 - (α - β) / 2 by ring]
    rw [Real.sin_add, Real.sin_sub]
    ring 
  have hcosne : Real.cos ((α - β) / 2) ≠ 0 := by 
    by_contra hcos 
    have h1 := h3a 
    rw [hcos] at h1 
    have h1' : Real.cos α + Real.cos β = 0 := by 
      linarith 
    linarith [h1', eq5] 
  have hcosne2 : Real.cos ((α + β) / 2) ≠ 0 := by 
    by_contra hcos 
    have h1 := h3a 
    rw [hcos] at h1 
    have h1' : Real.cos α + Real.cos β = 0 := by 
      linarith 
    linarith [h1', eq5] 
  have htan1 : Real.tan ((α + β) / 2) = 3 / 4 := by 
    have htan_eq : Real.sin ((α + β) / 2) / Real.cos ((α + β) / 2) = 3 / 4 := by 
      have h8 : Real.sin ((α + β) / 2) * Real.cos ((α - β) / 2) = 3 / 10 := by 
        nlinarith [h3b, eq6] 
      have h9 : Real.cos ((α + β) / 2) * Real.cos ((α - β) / 2) = 2 / 5 := by 
        nlinarith [h3a, eq5] 
      have htan' : Real.sin ((α + β) / 2) / Real.cos ((α + β) / 2) = (Real.sin ((α + β) / 2) * Real.cos ((α - β) / 2)) / (Real.cos ((α + β) / 2) * Real.cos ((α - β) / 2)) := by 
        field_simp [hcosne] 
        all_goals ring 
      rw [htan']
      rw [h8, h9] 
      norm_num 
    rw [Real.tan_eq_sin_div_cos]
    linarith [htan_eq]
  have htan2 : Real.tan (α + β) = 24 / 7 := by 
    have htan' : Real.tan ((α + β) / 2) = 3 / 4 := htan1 
    have : α + β = 2 * ((α + β) / 2) := by ring 
    rw [this, Real.tan_two_mul] 
    all_goals norm_num [htan']
  exact_mod_cast htan2