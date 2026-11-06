import Mathlib

theorem algebra_609271:
  {(a, b): ℂ × ℂ | a ^ 2 + b ^ 2 ≠ 0 ∧ a + 10 * b / (a ^ 2 + b ^ 2) = 5 ∧ b + 10 * a / (a ^ 2 + b ^ 2) = 4} =
  {(1, 2), (4, 2), (5 / 2, 2 + 3 / 2 * Complex.I), (5 / 2, 2 - 3 / 2 * Complex.I)} := by

  ext ⟨a, b⟩
  simp
  constructor
  . intro ⟨h1, h2, h3⟩
    -- prove $(2a - 5)(b - 2) = 0$ by $h2 * b + h3 * a$
    have h1' : 2 * a * b + 10 / (a ^ 2 + b ^ 2) * (a ^ 2 + b ^ 2) = 4 * a + 5 * b := by linear_combination h2 * b + h3 * a
    rw [div_mul_cancel₀ _ h1] at h1'
    replace h1' : (2 * a - 5) * (b - 2) = 0 := by linear_combination h1'
    simp at h1'

    -- cancel the division
    replace h2 := congr_arg (λ x ↦ x * (a ^ 2 + b ^ 2)) h2
    replace h3 := congr_arg (λ x ↦ x * (a ^ 2 + b ^ 2)) h3
    simp only [add_mul, div_mul_cancel₀ _ h1] at h3 h2

    -- so $a = \frac 5 2$ or $b = 2$
    match h1' with
    | Or.inl h1' =>
      -- $a = \frac 5 2$
      -- solve the quadratic equation to get $b = 2 \pm \frac 3 2 i$
      have ha : a = 5 / 2 := by linear_combination h1' / 2
      rw [ha, <-sub_eq_zero] at h2
      ring_nf at h2
      replace h2: (-5 / 2) * (b * b) + 10 * b + (-125 / 8) = 0 := by linear_combination h2
      have discrim' : discrim (-5 / 2 : ℂ) 10 (-125 / 8) = (15 / 2 * Complex.I) * (15 / 2 * Complex.I) := by
        unfold discrim
        ring_nf
        rw [sq, Complex.I_mul_I]
        ring_nf
      rw [quadratic_eq_zero_iff (by norm_num) discrim' _] at h2
      ring_nf at h2

      right
      right
      simp [ha]
      ring_nf
      symm
      exact h2
    | Or.inr h1' =>
      -- $b = 2$
      -- solve the quadratic equation to get $a = 1$ or $a = 4$
      have hb := sub_eq_zero.1 h1'
      simp [hb]
      rw [hb, <-sub_eq_zero] at h3
      ring_nf at h3
      have : (a - 1) * (a - 4) = 0 := by linear_combination h3 / -2
      simp at this
      rw [sub_eq_zero, sub_eq_zero] at this
      rw [<-or_assoc]
      left
      exact this
  . -- verify all result satisfy condition
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    . -- verify (1,2)
      constructor
      . norm_num
      . constructor
        . field_simp
          norm_num
        . field_simp
          norm_num
    . -- verify (4,2)
      constructor
      . norm_num
      . constructor
        . field_simp
          norm_num
        . field_simp
          norm_num
    . -- verify (5/2, 2 + 3/2 i)
      constructor
      . -- $a^2 + b^2 ≠ 0$
        norm_num [Complex.ext_iff, pow_two, Complex.I_mul_I]
        <;> ring_nf <;> norm_num
      . constructor
        . -- $a + \frac{10b}{a^2 + b^2} = 5$
          field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
          <;> ring_nf <;> norm_num
        . -- $b + \frac{10a}{a^2 + b^2} = 4$
          field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
          <;> ring_nf <;> norm_num
    . -- verify (5/2, 2 - 3/2 i)
      constructor
      . -- $a^2 + b^2 ≠ 0$
        norm_num [Complex.ext_iff, pow_two, Complex.I_mul_I]
        <;> ring_nf <;> norm_num
      . constructor
        . -- $a + \frac{10b}{a^2 + b^2} = 5$
          field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
          <;> ring_nf <;> norm_num
        . -- $b + \frac{10a}{a^2 + b^2} = 4$
          field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
          <;> ring_nf <;> norm_num