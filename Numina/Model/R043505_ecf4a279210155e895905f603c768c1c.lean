import Mathlib

theorem algebra_20428 :
    {(a, b) : ℝ × ℝ | ∃ x : ℂ, x.im ≠ 0 ∧ x ^ 2 + a * x + b = 0 ∧ x ^ 3 = 343} = {(7, 49)} := by 
  ext ⟨a, b⟩ 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] 
  constructor 
  · -- First implication: existence of a non-real root x with x^2 + a x + b = 0 and x^3 = 343 implies (a, b) = (7, 49)
    rintro ⟨x, h1, h2, h3⟩ 
    have h4 : x ^ 3 = 343 := h3 
    have h5 : x ^ 2 + a * x + b = 0 := by 
      simpa using h2 
    have eq1 : x ^ 2 = -a * x - b := by 
      calc 
        x ^ 2 = x ^ 2 + a * x + b - a * x - b := by ring_nf 
        _ = (x ^ 2 + a * x + b) - a * x - b := by ring_nf 
        _ = 0 - a * x - b := by rw [h2] 
        _ = -a * x - b := by ring_nf 
    have eq2 : x ^ 3 = (a ^ 2 - b) * x + a * b := by 
      calc 
        x ^ 3 = x * x ^ 2 := by ring_nf 
        _ = x * (-a * x - b) := by rw [eq1] 
        _ = -a * x ^ 2 - b * x := by ring_nf 
        _ = -a * (-a * x - b) - b * x := by rw [eq1] 
        _ = (a ^ 2 - b) * x + a * b := by ring_nf 
    have eq_eq2343 : (a ^ 2 - b) * x + a * b = 343 := by 
      calc 
        (a ^ 2 - b) * x + a * b = x ^ 3 := by 
          rw [eq2]
        _ = 343 := by 
          simpa using h3
    have eq3 := congr_arg Complex.re eq_eq2343 
    have eq4 := congr_arg Complex.im eq_eq2343 
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, mul_assoc] at eq3 eq4 
    have hb : b = a ^ 2 := by 
      have h7 : (a ^ 2 - b : ℝ) = 0 := by 
        have eq4' : a ^ 2 - b = 0 ∨ x.im = 0 := by 
          ring_nf at eq4 ⊢ 
          tauto 
        cases eq4' with 
        | inl h9 => linarith 
        | inr h9 => 
          exfalso 
          apply h1 
          simpa using h9 
      linarith 
    -- Now to solve a^3
    have ha3 : a ^ 3 = 343 := by 
      norm_num [hb] at eq3 ⊢ 
      nlinarith 
    -- Solving a^3 = 343 in real numbers
    have ha1 : a = 7 := by 
      have h11 : a ^ 3 - 343 = 0 := by linarith 
      have h3 : (a - 7) * (a^2 + 7*a + 49) = 0 := by 
        ring_nf at h11 ⊢ 
        nlinarith 
      cases' (mul_eq_zero.1 h3) with h4 h5 
      · -- a - 7 = 0 
        linarith 
      · -- a^2 + 7 * a + 49 = 0 
        have h6 : a ^ 2 + 7 * a + 49 = 0 := by linarith 
        nlinarith [sq_nonneg (a + 7 / 2)]
    -- Now getting b
    have hb1 : b = 49 := by 
      rw [hb]
      nlinarith [ha1]
    simp [ha1, hb1]
  · -- Backward implication: (a, b) = (7, 49) implies there's a non-real root x such that x^2 + a x + b = 0 and x^3 = 343
    rintro (⟨rfl, rfl⟩)
    use (-7 / 2 + Complex.I * (7 * Real.sqrt 3 / 2))
    constructor
    · -- Check x has non-zero imaginary part 
      have h1 : Real.sqrt 3 > 0 := by 
        apply Real.sqrt_pos.2 
        all_goals linarith 
      simp [h1]
      all_goals linarith [h1]
    constructor
    · -- Show x^2 + 7 * x + 49 = 0 
      field_simp [pow_two, Complex.ext_iff, Complex.I_mul_I, mul_add, mul_sub, mul_assoc]
      ring_nf 
      <;> norm_num [Real.sqrt_sq, Real.sqrt_pos.mpr]
      <;> nlinarith 
    · -- Show x^3 = 343 
      simp [pow_three, Complex.ext_iff, Complex.I_mul_I, mul_add, mul_sub, mul_assoc]
      ring_nf 
      <;> norm_num [Real.sqrt_sq, Real.sqrt_pos.mpr]
      <;> ring_nf 
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]