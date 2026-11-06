import Mathlib
open Real Complex

/-- Let $ f(n) = \left(\frac{-1 + i\sqrt{3}}{2}\right)^n + \left(\frac{-1 - i\sqrt{3}}{2}\right)^n $.
    What is f(2022)?
    (A) −2(B) −1(C) 0(D) 3(E) 2 -/
theorem algebra_95316 {f : ℕ → ℂ} (hf : ∀ n, f n = ((-1 + I * sqrt 3) / 2)^n + ((-1 - I * sqrt 3) / 2)^n) :
    f 2022 = 2 := by
  -- We can see that $\left(\frac{-1 + i\sqrt{3}}{2}\right)^3 = 1$ by
  -- multiplying out the cube and simplifying.
  have n1 : ((-1 + I * sqrt 3) / 2)^3 = 1 := by
    rw[div_pow, pow_succ, pow_two]
    field_simp
    ring_nf
    rw[← Complex.ofReal_pow, Real.sq_sqrt (by positivity), pow_three,
       pow_three, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), I_mul_I, I_sq]
    norm_num
    ring
  -- Similarly, $\left(\frac{-1 - i\sqrt{3}}{2}\right)^3 = 1$.
  have n2 : ((-1 - I * sqrt 3) / 2)^3 = 1 := by
    rw[div_pow, pow_succ, pow_two]
    field_simp
    ring_nf
    rw[← Complex.ofReal_pow, Real.sq_sqrt (by positivity), pow_three,
       pow_three, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), I_mul_I, I_sq]
    norm_num
    ring
  -- Hence $\left(\frac{-1 + i\sqrt{3}}{2}\right)^2022 = (\left(\frac{-1 + i\sqrt{3}}{2}\right)^3)^674 = 1^674 = 1$,
  -- and similarly for the other term, such that their sum f(2022) = 2.
  rw[hf, pow_eq_pow_mod _ n1, pow_eq_pow_mod _ n2]
  norm_num