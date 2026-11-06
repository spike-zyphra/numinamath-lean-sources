import Mathlib

open Polynomial

/- Let the roots of the polynomial $x^2 + 7x - 2$ be $\alpha$ and $\beta.$ Evaluate $\alpha^2 + \beta^2.$ -/
theorem algebra_21243 : Multiset.sum (Multiset.map (fun x ↦ x ^ 2) (X ^ 2 + C 7 * X - C 2 : ℝ[X]).roots) = 53 := by
  -- factors the polynomial into linear components
  have eq : ∀ a b, a = -7 / 2 - √57 / 2 → b = √57 / 2 - 7 / 2 → (X ^ 2 + C 7 * X - C 2 : ℝ[X]) = (X - C a) * (X - C b) := by
    intro a b aeq beq
    ring_nf
    ext i
    if hi : i ≤ 2 then
      interval_cases i
      simp only [X_mul_C, coeff_add, mul_coeff_zero, coeff_C_zero, coeff_X_zero, mul_zero, coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, zero_sub, zero_add, aeq, map_sub, beq, coeff_neg, zero_mul, neg_zero, sub_self, add_zero]
      ring_nf
      rw [Real.sq_sqrt (by linarith)]
      ring
      simp only [X_mul_C, coeff_add, coeff_mul_X, coeff_C_zero, coeff_sub, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte, coeff_C_succ, sub_self, add_zero, aeq, beq, ← map_mul, coeff_neg, neg_sub, sub_sub_sub_cancel_left]
      ring
      simp only [X_mul_C, coeff_add, coeff_mul_X, coeff_C_succ, coeff_sub, coeff_X_pow, ↓reduceIte, sub_zero, zero_add, coeff_neg, neg_zero, sub_self, coeff_mul_C, zero_mul, add_zero]
    else
      have ine0 : i ≠ 0 := by
        linarith
      have ine1 : 1 ≠ i := by
        linarith
      simp only [X_mul_C, coeff_add, coeff_C_mul, coeff_X, ine1, ↓reduceIte, mul_zero, coeff_sub, coeff_X_pow, coeff_C, ine0, sub_zero, zero_add, coeff_neg, neg_zero, sub_self, coeff_mul_C, zero_mul, add_zero]
  have peq := eq (-7 / 2 - √57 / 2) (√57 / 2 - 7 / 2) rfl rfl
  -- so the product equals $(-7 / 2 - \sqrt{57} / 2)^2+(\sqrt{57} / 2 - 7 / 2)^2 = 53$
  rw [peq, roots_mul, roots_X_sub_C, roots_X_sub_C]
  simp only [Multiset.singleton_add, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton]
  ring_nf
  rw [Real.sq_sqrt (by linarith)]
  ring
  simp only [ne_eq, mul_eq_zero, not_or]
  constructor
  exact X_sub_C_ne_zero (-7 / 2 - √57 / 2)
  exact X_sub_C_ne_zero (√57 / 2 - 7 / 2)
