import Mathlib

open Complex

/-
Simplify
$$
2 \cos ^{2}(\ln (2009) i)+i \sin (\ln (4036081) i)
$$

Answer: 4036082 / 4036081
-/
theorem algebra_608531 :
    2 * (cos ((Real.log 2009) * I))^2 + I * sin ((Real.log 4036081) * I)
    = 4036082 / 4036081 := by
  calc 2 * (cos ((Real.log 2009) * I))^2 + I * sin ((Real.log 4036081) * I)
    _ = 1 + cos ((2 : ℝ) * (Real.log 2009) * I) + I * sin ((Real.log 4036081) * I) := by
        simp [cos_sq]
        field_simp [mul_assoc]
    _ = 1 + cos ((Real.log 4036081) * I) + I * sin ((Real.log 4036081) * I) := by
        have help : (4036081 : ℝ) = 2009 ^ 2 := by norm_num
        rw [help, Real.log_pow]
        simp
    _ = 1 + cos ((Real.log 4036081) * I) + sin ((Real.log 4036081) * I) * I := by
        simp
        rw [mul_comm]
    _ = 1 + exp ((Real.log 4036081) * I * I) := by rw [exp_mul_I, add_assoc]
    _ = 1 + exp (-Real.log 4036081)          := by ring_nf; rw [I_sq]; simp
    _ = 1 + (1 / 4036081) := by
        rw [exp_neg, Complex.ofReal_log, exp_log]
        . field_simp
        . exact Ne.symm (OfNat.zero_ne_ofNat 4036081)
        . linarith
    _ = 4036082 / 4036081 := by group
