import Mathlib
open Complex

theorem algebra_609449 : (∀ n > 0, (∃ z : ℂ, 0 < z.re ∧ 0 < z.im ∧ z ^ n = ((starRingEnd ℂ) z) ^ n) → 3 ≤ n) ∧
  (∃ z : ℂ, 0 < z.re ∧ 0 < z.im ∧ z ^ 3 = ((starRingEnd ℂ) z) ^ 3) := by
  constructor
  · -- Assume that there exists a positive integer n, and a complex number z
    intro n hn ⟨z,hz1,hz2,hz3⟩
    by_contra h
    push_neg at h
    have h1 : n < 3 := by omega
    have h2 : n = 1 ∨ n = 2 := by 
      interval_cases n <;> tauto
    rcases h2 with (h2 | h2)
    · 
      rw [show n = 1 by omega] at hz3
      simp [pow_one] at hz3 
      have h3 : z.im = 0 := by 
        simp [Complex.ext_iff] at hz3 ⊢ 
        <;> nlinarith 
      nlinarith
    · 
      rw [show n = 2 by omega] at hz3 
      have h3 : z ^ 2 = ((starRingEnd ℂ) z) ^ 2 := by 
        simpa using hz3
      have eq1 := congr_arg Complex.re h3
      have eq2 := congr_arg Complex.im h3
      simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, 
        Complex.I_re, Complex.I_im] at eq1 eq2
      nlinarith 
  · -- Second part: existence of such z for n = 3
    use 1 + Complex.I * Real.sqrt 3 
    constructor 
    · -- Show Re z > 0
      norm_num 
    constructor 
    · -- Show Im z > 0
      have h1 : Real.sqrt 3 > 0 := by
        apply Real.sqrt_pos.mpr
        all_goals norm_num 
      have h2 : (1 + Complex.I * Real.sqrt 3).im = Real.sqrt 3 := by 
        simp [Complex.add_im, Complex.mul_im, Complex.I_im]
      rw [h2]
      linarith
    · -- Show z^3 = conjugate(z)^3 
      simp [pow_three, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Real.sqrt_sq]
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr]