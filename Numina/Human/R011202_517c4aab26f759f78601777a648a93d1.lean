import Mathlib

/- Solve for all complex numbers $z$ such that $z^{4}+4 z^{2}+6=z$.-/
theorem algebra_611431 :
    {z : ℂ | z ^ 4 + 4 * z ^ 2 + 6 = z} = {(1 - Complex.I * Real.sqrt 7) / 2, (1 + Complex.I * Real.sqrt 7) / 2, (-1 - Complex.I * Real.sqrt 11) / 2, (-1 + Complex.I * Real.sqrt 11) / 2} := by
  -- Split the goal into two parts.
  ext z
  simp
  apply Iff.intro
  . -- Assume that z⁴ + 4z² + 6 = z, prove that z is either of the four solutions.
    intro h₀
    -- Rewrite the equation to (z² - z + 2)(z² + z + 3) = 0.
    replace h₀ :  (z ^ 2 - z + 2) * (z ^ 2 + z + 3) = 0 := by linear_combination h₀
    simp at h₀
    cases h₀ with
    | inl h₀ =>
      -- If z² - z + 2 = 0, then z = (1 - i√7) / 2 or z = (1 + i√7) / 2.
      replace h₀ : (z - 1 / 2) ^ 2 = (Complex.I * Real.sqrt 7 / 2) ^ 2 := by
        rw [div_pow, mul_pow]
        norm_cast
        field_simp
        linear_combination 4 * h₀
      rw [sq_eq_sq_iff_eq_or_eq_neg] at h₀
      cases h₀ with
      | inl h₀ =>
        right
        left
        linear_combination h₀
      | inr h₀ =>
        left
        linear_combination h₀
    | inr h₀ =>
      -- If z² + z + 3 = 0, then z = (-1 - i√11) / 2 or z = (-1 + i√11) / 2.
      replace h₀ : (z + 1 / 2) ^ 2 = (Complex.I * Real.sqrt 11 / 2) ^ 2 := by
        rw [div_pow, mul_pow]
        norm_cast
        field_simp
        linear_combination 4 * h₀
      rw [sq_eq_sq_iff_eq_or_eq_neg] at h₀
      cases h₀ with
      | inl h₀ =>
        iterate 3 right
        linear_combination h₀
      | inr h₀ =>
        iterate 2 right
        left
        linear_combination h₀
  . -- Assume that z is either of the four solutions, prove that z⁴ + 4z² + 6 = z.
    intro h
    obtain ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ := h
    all_goals
      ring_nf
      apply Complex.ext
    all_goals
      simp [-one_div]
      repeat rw [show Complex.I ^ 3 = Complex.I * Complex.I ^ 2 by ring]
      field_simp
      norm_cast
      push_cast
      repeat rw [show Real.sqrt 7 ^ 3 = Real.sqrt 7 * Real.sqrt 7 ^ 2 by ring]
      repeat rw [show Real.sqrt 7 ^ 4 = Real.sqrt 7 ^ 2 * Real.sqrt 7 ^ 2 by ring]
      repeat rw [show Real.sqrt 11 ^ 3 = Real.sqrt 11 * Real.sqrt 11 ^ 2 by ring]
      repeat rw [show Real.sqrt 11 ^ 4 = Real.sqrt 11 ^ 2 * Real.sqrt 11 ^ 2 by ring]
      field_simp
      ring
