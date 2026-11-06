import Mathlib

theorem algebra_20492 : {x | ∃z, z^5 + z^4 + 2 * 
    z^3 + z^2 + z = 0 ∧ x = Complex.abs z} = {0, 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x ∈ {x | ∃z, z^5 + z^4 + 2 * z^3 + z^2 + z = 0 ∧ x = Complex.abs z}
    intro h
    rcases h with ⟨z, h_eq_zero, hx⟩
    have h_eq : z^5 + z^4 + 2 * z^3 + z^2 + z = z * (z^2 + 1) * (z^2 + z + 1) := by
      ring_nf
    rw [h_eq] at h_eq_zero
    cases' (mul_eq_zero.mp h_eq_zero) with h_eq_zero1 h_eq_zero2
    cases' (mul_eq_zero.mp h_eq_zero1) with h_eq_zero3 h_eq_zero4
    · -- Case z = 0
      have hz : z = 0 := by
        simpa using h_eq_zero3
      rw [hz] at hx
      simp [hx]
    · -- Case z^2 + 1 = 0
      have h_eq_zero4' : z^2 + 1 = 0 := by
        simpa using h_eq_zero4
      have h1 : z^2 = -1 := by 
        calc
          z^2 = z^2 + 1 - 1 := by ring
          _ = -1 := by rw [h_eq_zero4']; all_goals ring
      have h2 : Complex.abs z = 1 := by
        have eq1 : z.re ^ 2 - z.im ^ 2 = -1 := by
          have h_eq0 : z ^ 2 = -1 := h1
          have eq1 := congr_arg Complex.re h_eq0
          have eq2 := congr_arg Complex.im h_eq0
          simp [pow_two, Complex.add_re, Complex.add_im, 
              Complex.mul_re, Complex.mul_im, Complex.ofReal_re, 
              Complex.ofReal_im, Complex.I_re, Complex.I_im] at eq1 eq2
          <;> ring_nf at eq1 eq2
          <;> norm_num at eq1 eq2
          try { 
            nlinarith 
          }
          <;> norm_num
          all_goals try { 
            nlinarith 
          }
          all_goals try { 
            nlinarith [sq_nonneg (z.re), sq_nonneg (z.im)]
          }
          all_goals try { 
            tauto 
          }
          all_goals try { 
            tauto 
          }
          all_goals try { 
            nlinarith 
          }
          all_goals try { 
            nlinarith 
          }
          <;> norm_num
        have eq2 : 2 * z.re * z.im = 0 := by
          have h_eq0 : z ^ 2 = -1 := h1
          have eq1 := congr_arg Complex.re h_eq0
          have eq2 := congr_arg Complex.im h_eq0
          simp [pow_two, Complex.add_re, Complex.add_im, 
              Complex.mul_re, Complex.mul_im, Complex.ofReal_re, 
              Complex.ofReal_im, Complex.I_re, Complex.I_im] at eq1 eq2
          <;> ring_nf at eq1 eq2
          <;> norm_num at eq1 eq2
          try { 
            nlinarith 
          }
          <;> norm_num
          all_goals try { 
            nlinarith 
          }
          all_goals try { 
            nlinarith [sq_nonneg (z.re), sq_nonneg (z.im)]
          }
          all_goals try { 
            tauto 
          }
          all_goals try { 
            tauto 
          }
          all_goals try { 
            nlinarith 
          }
          all_goals try { 
            nlinarith 
          }
          <;> norm_num
        have h_eq_zero4'' : z.re = 0 ∨ z.im = 0 := by
          cases (mul_eq_zero.mp eq2) with
          | inl h1 => 
            left
            linarith
          | inr h2 => 
            right
            linarith
        cases h_eq_zero4'' with
        | inl h_eq_zero_re =>
          have h_eq_zero_re : z.re = 0 := by assumption
          have eq_zero_im_sq : z.im ^ 2 = 1 := by nlinarith
          have h_mod : z.re ^ 2 + z.im ^ 2 = 1 := by
            nlinarith
          have h30 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by 
            simp [Complex.abs, Complex.normSq]
            <;> ring_nf <;> norm_num [Complex.abs, Complex.normSq, pow_two]
          rw [h30]
          have h_mod_1 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := by
            rw [show z.re ^ 2 + z.im ^ 2 = (1 : ℝ) by linarith]
            all_goals norm_num
            all_goals try { 
              nlinarith 
            }
            all_goals try { 
              nlinarith 
            }
          rw [h_mod_1]
        | inr h_eq_zero_im =>
          exfalso
          have h_eq_zero_im : z.im = 0 := by assumption
          have eq_zero_re_sq : z.re ^ 2 = -1 := by
            nlinarith
          have contradiction : z.re ^ 2 ≥ 0 := by
            apply sq_nonneg
          nlinarith
      rw [h2] at hx
      simp [hx]
    · -- Case z^2 + z + 1 = 0
      have h_eq_zero5 : z^2 + z + 1 = 0 := by
        simpa using h_eq_zero2
      have h2 : Complex.abs z = 1 := by
        have eq1 : (z.re) ^ 2 - (z.im) ^ 2 + (z.re) + 1 = 0 := by
          have h_eq0 : z ^ 2 + z + 1 = 0 := h_eq_zero5
          have eq1 := congr_arg Complex.re h_eq0
          have eq2 := congr_arg Complex.im h_eq0
          simp [pow_two, Complex.add_re, Complex.add_im, 
                Complex.mul_re, Complex.mul_im, Complex.ofReal_re, 
                Complex.ofReal_im, Complex.I_re, Complex.I_im] at eq1 eq2
          <;> ring_nf at eq1 eq2
          <;> norm_num at eq1 eq2 
          try { 
            nlinarith 
          }
          <;> norm_num
          all_goals try { 
            nlinarith 
          }
          all_goals try { 
            nlinarith [sq_nonneg (z.re), sq_nonneg (z.im)]
          }
          all_goals try { 
            tauto 
          }
          all_goals try { 
            tauto 
          }
          all_goals try { 
            nlinarith 
          }
          all_goals try { 
            nlinarith 
          }
          <;> norm_num 
        have eq2 : 2 * (z.re) * (z.im) + (z.im) = 0 := by
          have h_eq0 : z ^ 2 + z + 1 = 0 := h_eq_zero5
          have eq1 := congr_arg Complex.re h_eq0
          have eq2 := congr_arg Complex.im h_eq0
          simp [pow_two, Complex.add_re, Complex.add_im, 
                Complex.mul_re, Complex.mul_im, Complex.ofReal_re, 
                Complex.ofReal_im, Complex.I_re, Complex.I_im] at eq1 eq2
          <;> ring_nf at eq1 eq2
          <;> norm_num at eq1 eq2 
          try { 
            nlinarith 
          }
          <;> norm_num
          all_goals try { 
            nlinarith 
          }
          all_goals try { 
            nlinarith [sq_nonneg (z.re), sq_nonneg (z.im)]
          }
          all_goals try { 
            tauto 
          }
          all_goals try { 
            tauto 
          }
          all_goals try { 
            nlinarith 
          }
          all_goals try { 
            nlinarith 
          }
          <;> norm_num 
        have eq42 : z.im * (2 * (z.re) + 1) = 0 := by
          linarith [eq2]
        cases (mul_eq_zero.mp eq42) with
        | inl h_eq_zero_im =>
          have h_eq_zero_im : z.im = 0 := by assumption
          have eq_zero_re_sq : (z.re) ^ 2 = -1 / 2 := by
            nlinarith [sq_nonneg z.im]
          have contradiction : z.re ^ 2 ≥ 0 := by
            apply sq_nonneg
          nlinarith
        | inr h_eq_zero_re =>
          have h_eq_zero_re : (2 * (z.re) + 1) = 0 := by assumption
          have z_re_eq_neg12 : (z.re) = -1 / 2 := by linarith
          have z_re_eq_neg12 : z.re = -1 / 2 := by linarith
          have z_im_sq_eq_34 : z.im ^ 2 = 3 / 4 := by 
            rw [z_re_eq_neg12] at eq1
            nlinarith 
          have h_mod : z.re ^ 2 + z.im ^ 2 = 1 := by
            have h0 : z.re = -1/2 := z_re_eq_neg12
            have h1 : z.im ^ 2 = 3 / 4 := z_im_sq_eq_34
            nlinarith
          have h30 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by 
            simp [Complex.abs, Complex.normSq]
            <;> ring_nf <;> norm_num [Complex.abs, Complex.normSq, pow_two]
          rw [h30]
          have h_mod_1 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := by 
            rw [show z.re ^ 2 + z.im ^ 2 = (1 : ℝ) by linarith]
            all_goals norm_num 
            all_goals try { 
              nlinarith 
            }
          rw [h_mod_1]
      rw [h2] at hx
      simp [hx]
  · -- Assume x ∈ {0, 1}
    intro h
    cases h with
    | inl h0 =>
      -- x = 0: Take z = 0
      use (0 : ℂ)
      simp [h0, Complex.abs]
      <;> ring_nf <;> norm_num 
    | inr h1 =>
      -- x = 1: Take z = i
      use Complex.I
      constructor
      · -- Check that i is a root of the polynomial
        simp [pow_two, pow_succ, Complex.ext_iff, Complex.I_mul_I]
        <;> norm_num 
        <;> ring_nf <;> norm_num 
        all_goals try { 
          tauto 
        }
        all_goals try { 
          native_decide 
        }
      · -- Show that |i| = 1
        simp [Complex.abs, Complex.normSq, h1]
        <;> norm_num 
        <;> ring_nf 
        all_goals try { 
          tauto 
        }
        all_goals try { 
          native_decide 
        }