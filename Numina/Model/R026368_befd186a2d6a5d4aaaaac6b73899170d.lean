import Mathlib

open Complex ComplexConjugate

theorem algebra_2928
  (a b c : ℂ)
  (h : ∀ z : ℂ, z.im ≠ 0 → (∃ r : ℝ, a * z ^ 2 + b * z + c = r)) :
  a = 0 ∧ b = 0 ∧ ∃ r : ℝ, c = r := by
  have eq1 := h Complex.I (by simp)
  rcases eq1 with ⟨r1, hr1⟩
  have eq2 := h (1 + Complex.I) (by simp)
  rcases eq2 with ⟨r2, hr2⟩
  have eq3 := h (2 + Complex.I) (by simp)
  rcases eq3 with ⟨r3, hr3⟩
  have eq4 := h (3 + 2 * Complex.I) (by simp)
  rcases eq4 with ⟨r4, hr4⟩
  have eq5 := h (2 + 3 * Complex.I) (by simp)
  rcases eq5 with ⟨r5, hr5⟩
  have eq1' := congr_arg Complex.im hr1
  have eq2' := congr_arg Complex.im hr2
  have eq3' := congr_arg Complex.im hr3
  have eq4' := congr_arg Complex.im hr4
  have eq5' := congr_arg Complex.im hr5
  simp [Complex.add_im, Complex.mul_im, pow_two, Complex.I_re, Complex.I_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at eq1' eq2' eq3' eq4' eq5'
  -- From these substitution $a \cdot I^2$.
  have ha1 : a.re = 0 := by
    ring_nf at eq1' eq2' eq3' eq4' eq5'
    nlinarith
  have ha2 : a.im = 0 := by
    ring_nf at eq1' eq2' eq3' eq4' eq5'
    nlinarith
  have hb1 : b.re = 0 := by
    ring_nf at eq1' eq2' eq3' eq4' eq5'
    nlinarith
  have hb2 : b.im = 0 := by
    ring_nf at eq1' eq2' eq3' eq4' eq5'
    nlinarith
  have ha11 : a = 0 := by
    rw [Complex.ext_iff]
    simp [ha1, ha2]
  have hb11 : b = 0 := by
    rw [Complex.ext_iff]
    simp [hb1, hb2]
  have hc1 : c.im = 0 := by
    ring_nf at eq1' eq2' eq3' eq4' eq5'
    nlinarith
  have hc2 : ∃ r : ℝ, c = r := by
    use c.re
    rw [Complex.ext_iff]
    simp [hc1]
  constructor
  · exact ha11
  constructor
  · exact hb11
  · exact hc2