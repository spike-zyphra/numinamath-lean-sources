import Mathlib

open Polynomial

/- Find the cubic polynomial, in $x,$ with integer coefficients that has $\cos 20^\circ$ as a root.  The coefficient of $x^3$ should be positive, and the coefficients should have no common factor other than 1. -/
theorem calculus_22737 (p : ℤ[X]) (hp : p = C 8 * X ^ 3 - C 6 * X - C 1) : p.natDegree = 3 ∧ (aeval (Real.cos (20 * Real.pi / 180))) p = 0 ∧ 0 < p.coeff 3 ∧ Finset.gcd {(p.coeff 3), (p.coeff 2), (p.coeff 1), (p.coeff 0)} id = 1 := by
  -- by the triple angle formula, \[\cos 3x = 4 \cos^3 x - 3 \cos x.\]Setting $x = 20^\circ,$ we get \[\cos 60^\circ = 4 \cos^3 20^\circ - 3 \cos 20^\circ,\]$
  have trieq := Real.cos_three_mul (20 * Real.pi / 180)
  have eq : Real.cos (3 * (20 * Real.pi / 180)) = Real.cos (Real.pi / 3) := by
    ring_nf
  constructor
  · -- $p$ is cubic
    have peq : p = C 8 * X ^ 3 + C 0 * X ^ 2 + C (-6) * X + C (-1) := by
      rw [hp]
      simp only [eq_intCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, zero_mul, add_zero, Int.reduceNeg, Int.cast_neg, neg_mul]
      ring_nf
    rw [peq]
    apply natDegree_cubic
    exact Ne.symm (OfNat.zero_ne_ofNat 8)
  constructor
  · -- $x = \cos 20^\circ$ is a root of $\boxed{8x^3 - 6x - 1}$
    rw [eq, Real.cos_pi_div_three] at trieq
    field_simp at trieq
    simp only [hp, Int.cast_ofNat, Int.cast_one, map_sub, map_mul, map_pow, aeval_X, map_one, aeval_C]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_ofNat]
    rw [trieq]
    ring
  constructor
  · -- the coefficient of $x^3$ is positive
    rw [hp]
    simp only [Int.cast_ofNat, Int.cast_one, coeff_sub, coeff_ofNat_mul, coeff_X_pow, ↓reduceIte, mul_one, sub_pos, coeff_C, coeff_C_mul, coeff_X]
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.one_ne_ofNat, mul_zero, sub_zero, Nat.ofNat_pos]
  · -- the coefficients should have no common factor other than 1
    simp only [hp, Int.cast_ofNat, Int.cast_one, coeff_sub, coeff_ofNat_mul, coeff_X_pow, ↓reduceIte, mul_one, Nat.reduceEqDiff, mul_zero, zero_sub, OfNat.one_ne_ofNat, coeff_X_one, Int.reduceNeg, OfNat.zero_ne_ofNat, coeff_X_zero, sub_self, coeff_one_zero, Finset.gcd_insert, id_eq, Finset.gcd_singleton, coeff_C_mul, coeff_X, coeff_C]
    have normeq : normalize (-1 : ℤ) = 1 := by
      exact rfl
    simp only [sub_zero, Int.reduceNeg, normeq, gcd_one_right]
