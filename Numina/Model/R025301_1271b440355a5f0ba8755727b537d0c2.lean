import Mathlib

theorem algebra_243593 (a : ℂ) (ha : a^5 + a + 1 = 0) :
    a^2 * (a - 1) = -1 ∨ a^2 * (a - 1) = (3 / 2) + (Real.sqrt 3 / 2) * .I ∨
    a^2 * (a - 1) = (3 / 2) - (Real.sqrt 3 / 2) * .I := by 
  have h1 : a^5 + a + 1 = (a^2 + a + 1) * (a^2 * (a - 1) + 1) := by 
    ring_nf 
  rw [h1] at ha
  cases (mul_eq_zero.1 ha) with 
  | inl h2 => 
    have h3 : a^2 + a + 1 = 0 := h2
    have ha1 : a^2 * (a - 1) = (3 / 2) + (Real.sqrt 3 / 2) * Complex.I ∨ 
      a^2 * (a - 1) = (3 / 2) - (Real.sqrt 3 / 2) * Complex.I := by 
      have h4 : a^2 + a + 1 = 0 := h3
      have h5 : a = (-1 + Complex.I * Real.sqrt 3) / 2 ∨ a = (-1 - Complex.I * Real.sqrt 3) / 2 := by 
        have h6 : a^2 + a + 1 = 0 := h4
        have h7 : a^2 + a + 1 = (a - (-1 + Complex.I * Real.sqrt 3) / 2) * (a - (-1 - Complex.I * Real.sqrt 3) / 2) := by
          ring_nf
          simp [Complex.ext_iff, pow_two, mul_add, sub_mul, mul_sub, mul_comm, mul_assoc]
          <;> ring_nf
          <;> simp [Real.sqrt_sq]
          <;> ring
        rw [h7] at h6 
        cases (mul_eq_zero.1 h6) with 
        | inl h8 => 
          left 
          have h9 : a = (-1 + Complex.I * Real.sqrt 3) / 2 := by 
            calc 
              a = (a - (-1 + Complex.I * Real.sqrt 3) / 2) + (-1 + Complex.I * Real.sqrt 3) / 2 := by ring_nf 
              _ = (-1 + Complex.I * Real.sqrt 3) / 2 := by 
                rw [h8] 
                all_goals ring_nf 
          assumption 
        | inr h8 => 
          right 
          have h9 : a = (-1 - Complex.I * Real.sqrt 3) / 2 := by 
            calc 
              a = (a - (-1 - Complex.I * Real.sqrt 3) / 2) + (-1 - Complex.I * Real.sqrt 3) / 2 := by ring_nf 
              _ = (-1 - Complex.I * Real.sqrt 3) / 2 := by 
                rw [h8] 
                all_goals ring_nf 
          assumption 
      cases h5 with 
      | inl h5 => 
        left 
        rw [h5] 
        field_simp [pow_two, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, 
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring_nf 
        <;> simp [Real.sqrt_sq] 
        <;> ring_nf 
      | inr h5 => 
        right 
        rw [h5] 
        field_simp [pow_two, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, 
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring_nf 
        <;> simp [Real.sqrt_sq] 
        <;> ring_nf 
    cases ha1 with 
    | inl h => 
      right 
      left 
      exact h 
    | inr h => 
      right 
      right 
      exact h 
  | inr h2 => 
    left
    have h4 : a^2 * (a - 1) + 1 = 0 := h2 
    have h5 : a^2 * (a - 1) = -1 := by 
      calc 
        a^2 * (a - 1) = (a^2 * (a - 1) + 1) - 1 := by ring_nf 
        _ = -1 := by 
          rw [h4] 
          all_goals ring_nf 
    exact h5