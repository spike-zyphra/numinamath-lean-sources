import Mathlib

/-Let $z$ be a complex number such that
\[z^5 + z^4 + 2z^3 + z^2 + z = 0.\]Find all possible values of $|z|.$

Enter all possible values, separated by commas.-/
theorem algebra_20492 : {x | ∃z, z^5 + z^4 + 2 * 
    z^3 + z^2 + z = 0 ∧ x = Complex.abs z} = {0, 1} := by
  ext x
  simp
  -- divide into two parts
  apply Iff.intro <;> intro h
  . obtain ⟨z, hz, hx⟩ := h
    rw [hx]
    clear hx
    -- facterize to z(z^2 + 1)(z^2 + z + 1)
    replace hz : z * (z ^ 2 + 1) * (z ^ 2 + z + 1) = 0 := by ring_nf at hz ⊢; exact hz
    -- split into three cases
    apply NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero at hz
    cases hz with
    | inr hz => -- when z ^ 2 + z + 1 = 0
      -- show that z ^ 3 = 1
      replace hz : (z - 1) * (z ^ 2 + z + 1) = 0 := by rw [hz]; norm_num
      replace hz : z ^ 3 = 1 := by
        ring_nf at hz
        calc
          z ^ 3 = (-1 + z ^ 3) + 1 := by ring_nf
          _ = 1 := by rw [hz]; norm_num

      right
      -- show that Complex.abs z ^ 3 = 1
      replace hz : Complex.abs z ^ 3 = 1 := by
        rw [<-Complex.abs_pow]
        rw [hz]
        norm_num

      -- cancel the power of 3, so we can get the answer
      rw [<-Complex.abs_abs] at hz ⊢
      rw [show (1 : ℝ) = 1 ^ 3 by norm_num] at hz
      rw [pow_left_inj₀] at hz
      exact hz
      repeat positivity
    -- when z(z ^ 2 + 1) = 0
    | inl hz =>
      apply NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero at hz
      cases hz with
      | inr hz => -- when z ^ 2 + 1 = 0
        -- show that z ^ 2 = -1
        replace hz : z ^ 2 = -1 := by
          calc
            z ^ 2 = (z ^ 2 + 1) - 1 := by ring_nf
            _ = -1 := by rw [hz]; norm_num
        right
        -- show that Complex.abs z ^ 2 = 1
        replace hz : Complex.abs z ^ 2 = 1 := by
          rw [<-Complex.abs_pow]
          rw [hz]
          norm_num
        -- cancel the power of 3, so we can get the answer
        rw [<-Complex.abs_abs] at hz ⊢
        rw [show (1 : ℝ) = 1 ^ 2 by norm_num] at hz
        rw [pow_left_inj₀] at hz
        exact hz
        repeat positivity

      | inl hz => -- when z = 0
        left
        rw [hz]
        norm_num
  . cases h with
    | inl hz => -- when z = 0
      use 0
      norm_num
      exact hz
    | inr hz => -- when |z| = 1
      use (√3 / 2 * Complex.I - 1 / 2)
      ring_nf
      refine ⟨?_, ?_⟩
      -- show that z^5 + z^4 + 2 * z^3 + z^2 + z = 0
      . calc -15 / 32 + (√3 : ℂ) * Complex.I * (21 / 32) + (√3 : ℂ) ^ 2 * Complex.I ^ 2 * (-7 / 16) + (√3 : ℂ) ^ 3 * Complex.I ^ 3 * (5 / 16) + (√3 : ℂ) ^ 4 * Complex.I ^ 4 * (-3 / 32) + (√3 : ℂ) ^ 5 * Complex.I ^ 5 * (1 / 32)
          = -15 / 32 + (√3 : ℂ) * Complex.I * (21 / 32) + (√3 : ℂ) ^ 2 * Complex.I ^ 2 * (-7 / 16) + (√3 : ℂ) ^ 2 * (√3 : ℂ) * Complex.I ^ 2 * Complex.I * (5 / 16) + ((√3 : ℂ) ^ 2) ^ 2 * (Complex.I ^ 2) ^ 2 * (-3 / 32) + ((√3 : ℂ) ^ 2) ^ 2 * (√3 : ℂ) * (Complex.I ^ 2) ^ 2 * Complex.I * (1 / 32) := by ring_nf
          _ = -15 / 32 + (√3 : ℂ) * Complex.I * (21 / 32) + 3 * (-1) * (-7 / 16) + 3 * (√3 : ℂ) * (-1) * Complex.I * (5 / 16) + 9 * (-3 / 32) + 9 * (√3 : ℂ) * Complex.I * (1 / 32) := by rw [show (√3 : ℂ) ^ 2 = 3 by norm_cast; rw [Real.sq_sqrt]; norm_num, show Complex.I ^ 2 = -1 by rw [<-Complex.I_mul_I]; ring_nf]; ring_nf
          _ = 0 := by ring_nf
      . symm
        calc
          Complex.abs (-1 / 2 + (√3 : ℂ) * Complex.I * (1 / 2)) = Complex.abs ((-1 / 2 : ℂ) + (√3 / 2 : ℂ) * Complex.I) := by ring_nf
          _ = √((-1 / 2) ^ 2 + (√3 / 2) ^ 2) := by rw [<-Complex.abs_add_mul_I]; norm_cast
          _ = 1 := by ring_nf; rw [Real.sq_sqrt]; norm_num; norm_num
          _ = x := by rw [hz]