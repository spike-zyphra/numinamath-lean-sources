import Mathlib

theorem algebra_299568 {a b : ℂ} (f : ℂ → ℂ) (hf : ∀ z, ‖z‖ = 1 → ‖f z‖ = 1)
    (h : ∀ z, f z = z ^ 2 + a * z + b) :
    a = 0 ∧ b = 0 := by 
  have eq1 := hf 1 (by 
    norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  )
  rw [h] at eq1 
  have eq11 := eq1
  simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq] at eq11 
  have eq2 := hf (-1) (by 
    norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  )
  rw [h] at eq2
  have eq22 := eq2 
  simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq] at eq22
  have eq3 := hf (Complex.I) (by 
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  )
  rw [h] at eq3 
  have eq33 := eq3
  simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, pow_two] at eq33 
  have eq4 := hf (-Complex.I) (by 
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  )
  rw [h] at eq4 
  have eq44 := eq4 
  simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, pow_two] at eq44 
  have eq111 : a.re = 0 := by
    norm_num [Complex.ext_iff] at eq11 eq22 eq33 eq44 ⊢ 
    ring_nf at eq11 eq22 eq33 eq44 
    nlinarith 
  have eq112 : a.im = 0 := by 
    norm_num [Complex.ext_iff] at eq11 eq22 eq33 eq44 ⊢ 
    ring_nf at eq11 eq22 eq33 eq44 
    nlinarith 
  have eq113 : b.re = 0 := by 
    norm_num [Complex.ext_iff] at eq11 eq22 eq33 eq44 ⊢ 
    ring_nf at eq11 eq22 eq33 eq44 
    nlinarith
  have eq114 : b.im = 0 := by 
    norm_num [Complex.ext_iff] at eq11 eq22 eq33 eq44 ⊢ 
    ring_nf at eq11 eq22 eq33 eq44 
    nlinarith 
  constructor 
  · -- a = 0 
    simp [Complex.ext_iff, eq111, eq112] 
  · -- b = 0 
    simp [Complex.ext_iff, eq113, eq114]