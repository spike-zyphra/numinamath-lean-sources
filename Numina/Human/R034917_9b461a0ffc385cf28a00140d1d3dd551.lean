import Mathlib

open Polynomial
open Complex

/- Find the ordered pair $(a,b)$ of real numbers for which
\[(ax + b)(x^5 + 1) - (5x + 1)\]is divisible by $x^2 + 1.$ -/
theorem algebra_20392 {a b : ℝ} :
    (X ^ 2 + C 1) ∣ (C a * X + C b) * (X ^ 5 + C 1) - (C 5 * X + C 1) → (a, b) = (2, 3) := by
  intro dvd
  rcases dvd with ⟨p, heq⟩
  -- let $x = i$ we get (-a + b - 1) + (a + b - 5)i = 0$
  apply congrArg (fun x ↦ (aeval I) x) at heq
  simp only [map_one, map_sub, map_mul, map_add, aeval_C, coe_algebraMap, aeval_X, map_pow, ofReal_ofNat, I_sq, neg_add_cancel, zero_mul] at heq
  have fiveeq : 5 = 4 + 1 := by
    exact rfl
  rw [fiveeq, pow_add, I_pow_four] at heq
  -- so $b - a - 1 = 0$ and $b + a - 5 = 0$
  have heq2 := heq
  apply congrArg (fun x ↦ x.re) at heq
  simp only [pow_one, one_mul, sub_re, mul_re, add_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, zero_add, one_re, add_im, mul_im, add_zero, one_im, re_ofNat, im_ofNat, zero_re] at heq
  apply congrArg (fun x ↦ x.im) at heq2
  simp only [pow_one, one_mul, sub_im, mul_im, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, zero_add, add_im, one_im, add_zero, one_re, re_ofNat, im_ofNat, zero_im] at heq2
  -- solve this we get $a = 2$ and $b = 3$
  ext
  any_goals
  simp only
  linarith