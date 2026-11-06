import Mathlib

/- 26th BMO 1990 Problem 2 The fractional part { x } of a real number is defined as x - [x]. Find a positive real x such that { x } + { 1/x } = 1 (*). Is there a rational x satisfying (*)? -/

theorem number_theory_124291 :
    (∃ x : ℝ, x > 0 ∧ Int.fract x + Int.fract (1 / x) = 1) ∧
    ¬∃ q : ℚ, q > 0 ∧ Int.fract q + Int.fract (1 / q) = 1 := by

  constructor
  -- We first show that there exists a positive real number x such that { x } + { 1/x } = 1.
  -- We can take x = 2 + √3.
  · use 2 + Real.sqrt 3
    constructor
    -- It is positive as it is sum of positive numbers.
    · apply add_pos
      · linarith
      · exact Real.sqrt_pos.2 (by norm_num)
    · norm_num
      -- The fractionary part of 2 + √3 is 2 + √3 - 3 = √3 - 1
      have h1 : Int.fract √3 = √3 - 1 := by
        rw [Int.fract_eq_iff]
        constructor
        · simp
        · constructor
          · suffices √3 < 2 by linarith
            rw [Real.sqrt_lt]
            all_goals norm_num
          · use 1; ring
      -- The fractionary part of 1/(2 + √3) is its self, as it is less than 1.
      have h2 : Int.fract (2 + √3)⁻¹ = (2 + √3)⁻¹ := by
        simp only [Int.fract_eq_self, inv_nonneg]
        have := lt_add_of_pos_right 2 (Real.sqrt_pos.mpr (by norm_num : 0 < (3 : ℝ)))
        constructor
        · linarith
        · rw [inv_lt_one_iff₀]; right; linarith
      -- The rest is just algebra.
      rw [h1, h2]
      field_simp
      rw [mul_add, sub_mul, sub_mul, ← sub_eq_zero, Real.mul_self_sqrt (by linarith)]
      ring
  -- Now we show that there is no positive rational number x such that { x } + { 1/x } = 1 by contradiction.
  · by_contra!
    obtain ⟨x, hpos, h⟩ := this
    -- We can assume that x >= 1, as otherwise we can just take 1/x.
    wlog h1 : x >= 1
    · apply this (1/x)
      · simp only [one_div, gt_iff_lt, inv_pos]; exact hpos
      · simp only [one_div, div_inv_eq_mul, one_mul]
        rw [one_div, add_comm] at h
        exact h
      · rw [ge_iff_le, one_le_div hpos]
        exact le_of_not_ge (this x hpos h)
    -- x = 1 obviously doesn't work, so we can assume x > 1.
    · by_cases h1' : x = 1
      · subst h1'
        simp at h
      · have hx := h
        -- Again, the fractionary part of 1/x is its self, as it is less than 1.
        have : Int.fract (1/x) = 1/x := by
          rw [Int.fract_eq_self]
          constructor
          · rw [one_div, inv_nonneg]; exact le_of_lt hpos
          · exact Bound.div_lt_one_of_pos_of_lt hpos (lt_of_le_of_ne h1 fun a ↦ h1' (id (Eq.symm a)))
        rw [this, Eq.symm (Rat.num_div_den x), one_div, inv_div] at h
        -- Since x = p/q is positive, if we assume that q > 0, then its p > 0 as well.
        -- We can also assume that p and q are coprime, as otherwise we can just divide them by their gcd.
        have ppos : x.num > 0 := by simp [hpos]
        obtain ⟨p, q, hq, cop⟩ := x
        dsimp at *
        -- We multiply the equation by p*q, which is positive.
        rw [Int.fract_div_intCast_eq_div_intCast_mod, ← mul_right_cancel_iff_of_pos
            (by simp [ppos, Nat.zero_lt_of_ne_zero hq] : p * q > (0 : ℚ)), add_mul, ← sub_eq_zero] at h
        ring_nf at h
        rw [mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr hq),
            mul_inv_cancel_right₀ (by exact Ne.symm (ne_of_lt hpos)), ← sub_mul] at h
        -- Taking the equation mod q, we get that p^2 % q = 0.
        have : (↑(p % ↑q) - ↑q) * ↑p + ↑q ^ 2 = (0 : ZMod q) := by rw_mod_cast [h]; simp
        simp only [ZMod.intCast_mod, CharP.cast_eq_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, add_zero] at this
        rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
        -- This means that p^2 is divisible by q. But since p and q are coprime, this means that q = 1.
        have : q ∣ p.natAbs * p.natAbs := by zify; simp [this]
        nth_rw 1 [← mul_one p.natAbs] at this
        apply Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_comm.mp cop) at this
        apply Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp cop) at this
        simp only [Nat.dvd_one] at this
        simp only [this, Rat.mk_den_one, Int.fract_intCast, one_div, zero_add] at hx
        -- But this is impossible, as otherwise x is an integer, and we would have 1/x = 1. But x = 1 doesn't work.
        exact ne_of_lt (Int.fract_lt_one (p : ℚ)⁻¹) hx