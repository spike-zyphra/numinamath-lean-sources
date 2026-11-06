import Mathlib

-- Find c if a, b, and c are positive integers which satisfy c = (a + bi)^3 - 107i.

theorem AIME_algebra_94794 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h : c = (a + b * Complex.I)^3 - 107 * Complex.I) : c = 198 := by

  -- We rewrite the equation
  have : (c + 3 * a * b * b - a * a * a) + (b * b * b - 3 * a * a * b + 107) * Complex.I = 0 := by
    calc (c + 3 * a * b * b - a * a * a) + (b * b * b - 3 * a * a * b + 107) * Complex.I
        = (a + b * Complex.I)^3 - 107 * Complex.I + 3 * a * b * b - a * a * a + (b * b * b - 3 * a * a * b + 107)  * Complex.I := by rw [h]
      _ = ↑a * ↑b ^ 2 * 3 + ↑a * ↑b ^ 2 * Complex.I ^ 2 * 3 + ↑b ^ 3 * Complex.I + ↑b ^ 3 * Complex.I ^ 3 := by ring_nf
      _ = ↑a * ↑b ^ 2 * 3 + ↑a * ↑b ^ 2 * -1 * 3 + ↑b ^ 3 * Complex.I + ↑b ^ 3 * (Complex.I * -1)  := by rw [pow_two Complex.I, pow_three Complex.I, Complex.I_mul_I]
      _ = 0 := by ring

  -- We split the equation into real and imaginary parts
  obtain ⟨re, im⟩ := Complex.ext_iff.mp this
  simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, Complex.intCast_im, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero,
    Complex.I_re, Complex.add_im, Complex.sub_im, zero_add, Complex.I_im, mul_one, zero_sub,
    neg_sub, Complex.zero_re, Complex.zero_im] at re im

  -- We show that b is 1 or 107
  have : b = 1 ∨ b = 107 := by
    rw [← Int.natAbs_of_nonneg (Int.le_of_lt hb)]
    apply Or.imp (congrArg Nat.cast) (congrArg Nat.cast) --this
    apply (Nat.dvd_prime (by norm_num : Nat.Prime 107)).mp
    apply Int.ofNat_dvd_right.mp
    apply Dvd.intro (3 * a * a - b * b)
    symm
    rw_mod_cast [← sub_eq_zero]
    rw[← @Int.cast_inj Real,Int.cast_zero,←im]
    norm_num
    ring_nf

  rcases this with h1 | h107
  -- If b = 1, then we make the substitutions and get a = 6 and c = 198
  · simp_rw [h1] at re im
    have : a = 6 := by
      ring_nf at im
      rw [sub_eq_zero, (by norm_num : (108 : ℝ) = 6^2 * 3)] at im
      simp only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false] at im
      rw [sq_eq_sq₀ (by norm_num) (by apply Int.cast_nonneg.mpr; linarith)] at im
      exact_mod_cast im.symm
    rw [this, sub_eq_zero, ← eq_sub_iff_add_eq] at re
    norm_num at re
    exact_mod_cast re
  -- If b = 107, then we get a contradiction looking modulo 3
  · simp_rw [h107] at re im
    have int_cast : 107 * 107 * 107 - 3 * a * a * 107 + 107 = 0 := by
      norm_num at im
      rw[←@Int.cast_inj ℝ]
      norm_num
      rw[im]
    rw [sub_add_eq_add_sub, sub_eq_zero] at int_cast
    repeat rw [mul_assoc 3 _ _] at int_cast
    apply_fun (fun x ↦ x % 3) at int_cast
    simp at int_cast