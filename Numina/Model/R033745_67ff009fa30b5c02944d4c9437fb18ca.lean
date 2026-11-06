import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_16295 {f : ℂ → ℂ}
    (hf : f = fun z => ((-1 + I * √ 3) * z + (-2 * √ 3 - 18 * I)) / 2) :
    {c : ℂ | ∃ t : ℝ, ∀ z, f z - c = Complex.exp (Complex.I * t) * (z - c)} = {√ 3 - 5 * I} := by
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume c is a center of rotation, prove c = √3 - 5i
    rintro ⟨t, ht⟩
    have eq1 := ht c
    have eq2 : f c = c := by
      simp [sub_eq_zero] at eq1 ⊢
      try tauto
    rw [hf] at eq2
    simp at eq2
    have eq4 := eq2
    simp [Complex.ext_iff, mul_add, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq4
    ring_nf at eq4
    have eq5 : c.re = Real.sqrt 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3]
    have eq6 : c.im = -5 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3]
    have hc : c = Real.sqrt 3 - 5 * Complex.I := by
      simp [Complex.ext_iff, eq5, eq6]
    exact_mod_cast hc
  · -- Assume c = √3 - 5i, prove c is a center of rotation
    intro hc
    rw [hc]
    use (Real.pi * (2 / 3))
    intro z
    have eq1 : ((-1 + I * √ 3) * z + (-2 * √ 3 - 18 * I)) / 2 - (Real.sqrt 3 - 5 * Complex.I) = Complex.exp (Complex.I * (Real.pi * (2 / 3))) * (z - (Real.sqrt 3 - 5 * Complex.I)) := by
      simp [Complex.ext_iff, mul_add, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im]
      ring_nf
      have h1 : Real.cos (Real.pi * (2 / 3)) = -1 / 2 := by
        have h2 : Real.cos (Real.pi * (2 / 3)) = -1 / 2 := by
          have h3 : Real.pi * (2 / 3) = Real.pi - Real.pi / 3 := by ring
          rw [h3]
          rw [Real.cos_pi_sub]
          norm_num
        exact h2
      have h2 : Real.sin (Real.pi * (2 / 3)) = Real.sqrt 3 / 2 := by
        have h3 : Real.sin (Real.pi * (2 / 3)) = Real.sqrt 3 / 2 := by
          have h4 : Real.pi * (2 / 3) = Real.pi - Real.pi / 3 := by ring
          rw [h4]
          rw [Real.sin_pi_sub]
          have h5 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
          linarith
        exact h3
      rw [h1, h2]
      ring_nf
      <;> norm_num [Real.sqrt_mul_self, pow_two]
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3]
    simpa [hf] using eq1