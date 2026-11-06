import Mathlib

open Complex
open Polynomial

/- Let the roots of
\[z^3 = 2 + 2i\]be $a_1 + ib_1,$ $a_2 + ib_2,$ and $a_3 + ib_3.$  Compute $a_1 a_2 a_3.$ -/
theorem algebra_21810 : Multiset.prod (Multiset.map (fun (x : ℂ) ↦ x.re) (X ^ 3 - C (2 + 2 * I)).roots) = 1 / 2 := by
  -- $i ^ 3 = -i$
  have Icubic : I ^ 3 = -I := by
    rw [← two_add_one_eq_three, pow_add, I_sq]
    ring
  -- $\sqrt{3} ^ 2 = 3$
  have sqrt3sq : (√3 : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by exact zero_le_three)]
    exact rfl
  -- $X ^ 3 - (2 + 2 * i) = (X - (-1 + i)) * (X - (1 / 2 + \sqrt{3} / 2 + (\sqrt{3} / 2 - 1 / 2) * i)) * (X - (1 / 2 - \sqrt{3} / 2 + (-\sqrt{3} / 2 - 1 / 2) * i))$
  have eq : ∀ a b c, a = -1 + I → b = 1 / 2 + √3 / 2 + (√3 / 2 - 1 / 2) * I → c = 1 / 2 - √3 / 2 + (-√3 / 2 - 1 / 2) * I → X ^ 3 - C (2 + 2 * I) = (X - C a) * (X - C b) * (X - C c) := by
    intro a b c aeq beq ceq
    ring_nf
    simp only [← map_mul, mul_assoc]
    -- we show that the coefficients of both sides are equal
    ext i
    if hi : i ≤ 3 then
      interval_cases i
      -- coeff 0
      simp only [map_add, map_mul, coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, coeff_add, coeff_C_zero, mul_coeff_zero, zero_sub, neg_add_rev, X_pow_mul_C, coeff_X_zero, zero_mul, add_zero, mul_zero, sub_self, coeff_neg, neg_zero, zero_add]
      rw [aeq, beq, ceq]
      ring_nf
      simp only [one_div, sqrt3sq, I_sq, neg_mul, one_mul, Icubic]
      ring
      -- coeff 1
      simp only [map_add, map_mul, coeff_sub, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte, coeff_add, coeff_C_succ, coeff_mul_C, zero_mul, add_zero, sub_self, X_pow_mul_C, coeff_X_mul, mul_coeff_zero, coeff_C_zero, coeff_C_mul, mul_zero, sub_zero, coeff_neg, neg_zero]
      rw [aeq, beq, ceq]
      ring_nf
      simp only [one_div, sqrt3sq, I_sq, neg_mul, one_mul, Icubic]
      ring
      -- coeff 2
      simp only [map_add, map_mul, coeff_sub, coeff_X_pow, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, ↓reduceIte, coeff_add, coeff_C_succ, coeff_mul_C, zero_mul, add_zero, sub_self, X_pow_mul_C, coeff_X_mul, coeff_C_mul, mul_one, zero_sub, zero_add, coeff_neg, mul_zero]
      rw [aeq, beq, ceq]
      ring_nf
      -- coeff 3
      simp only [map_add, map_mul, coeff_sub, coeff_X_pow, ↓reduceIte, coeff_add, coeff_C_succ, coeff_mul_C, zero_mul, add_zero, sub_zero, X_pow_mul_C, coeff_X_mul, coeff_C_mul, OfNat.ofNat_eq_ofNat, Nat.succ_ne_self, mul_zero, sub_self, coeff_neg, neg_zero, zero_add]
    else 
      -- else $3 < i$, and the coefficients of both sides are zero
      simp only [map_add, coeff_sub, coeff_X_pow, coeff_add, X_mul_C, X_pow_mul_C, coeff_C_mul, mul_assoc, mul_ite, mul_one, mul_zero, coeff_neg]
      have ine0 : i ≠ 0 := by
        linarith
      have ine1 : 1 ≠ i := by
        linarith
      have ine2 : i ≠ 2 := by
        linarith
      have ine3 : i ≠ 3 := by
        linarith
      simp only [ine3, ↓reduceIte, coeff_C, ine0, map_mul, coeff_mul_C, zero_mul, add_zero, sub_self, coeff_X, ine1, mul_zero, ine2, neg_zero, coeff_C_mul]
  have peq : X ^ 3 - C (2 + 2 * I) = (X - C (-1 + I)) * (X - C (1 / 2 + √3 / 2 + (√3 / 2 - 1 / 2) * I)) * (X - C (1 / 2 - √3 / 2 + (-√3 / 2 - 1 / 2) * I)) := by
    rw [eq]
    exact rfl
    exact rfl
    exact rfl
  -- so the roots of $X ^ 3 - (2 + 2 * i)$ are $-1 + i, 1 / 2 + \sqrt{3} / 2 + (\sqrt{3} / 2 - 1 / 2) * i, 1 / 2 - \sqrt{3} / 2 + (-\sqrt{3} / 2 - 1 / 2) * i$
  rw [peq, roots_mul, roots_mul, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  simp only [one_div, Multiset.singleton_add, Multiset.cons_add, Multiset.map_cons, add_re, neg_re, one_re, I_re, add_zero, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self', div_ofNat_re, ofReal_re, mul_re, sub_re, mul_zero, sub_im, div_ofNat_im, ofReal_im, zero_div, inv_im, im_ofNat, neg_zero, sub_self, I_im, mul_one, Multiset.map_singleton, neg_im, Multiset.prod_cons, Multiset.prod_singleton, neg_mul, one_mul]
  -- the product of real parts of roots is $1 / 2$
  ring_nf
  rw [Real.sq_sqrt (by linarith)]
  ring
  -- the multiplication of linear polynomials are nonzero
  by_contra contra
  rw [mul_eq_zero] at contra
  rcases contra with contra | contra
  have : X - C (-1 + I) ≠ 0 := by
    exact X_sub_C_ne_zero _
  contradiction
  have : X - C (1 / 2 + ↑√3 / 2 + (↑√3 / 2 - 1 / 2) * I) ≠ 0 := by
    exact X_sub_C_ne_zero _
  contradiction
  by_contra contra
  rw [mul_assoc, mul_eq_zero, mul_eq_zero] at contra
  rcases contra with contra | contra | contra
  have : X - C (-1 + I) ≠ 0 := by
    exact X_sub_C_ne_zero _
  contradiction
  have : X - C (1 / 2 + ↑√3 / 2 + (↑√3 / 2 - 1 / 2) * I) ≠ 0 := by
    exact X_sub_C_ne_zero _
  contradiction
  have : X - C (1 / 2 - ↑√3 / 2 + (-↑√3 / 2 - 1 / 2) * I) ≠ 0 := by
    exact X_sub_C_ne_zero _
  contradiction


  