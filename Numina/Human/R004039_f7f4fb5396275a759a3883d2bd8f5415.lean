import Mathlib


/-- Given that the complex number satisfies $x^{2}+x+1=0$,
    find the value of $x^{14}+\frac{1}{x^{14}}$. -/
theorem algebra_232657 {x : ℂ} (hx : x ^ 2 + x + 1 = 0) :
    x ^ 14 + 1 / x ^ 14 = -1 := by
  -- We have $x^3 = 1$:
  have isroot : x ^ 3 = 1 := by
    -- Clearly, $x^2 = - (x + 1)$, 
    have : x ^ 2 = - (x + 1) := by rwa[eq_neg_iff_add_eq_zero, ← add_assoc]
    -- hence $x^3 = - (x+1) x = -x^2 - x = (x + 1) - x = 1$.
    rw[pow_succ, this, neg_add, add_mul, neg_mul, ← pow_two, this]
    ring
  -- So, $1/x^3 = 1$, too.
  have invisroot : 1 / x ^ 3 = 1 := by rw[isroot]; norm_num
  -- Therefore, $x^{14} = (x^3)^4 x^2 = x^2$,
  have x14 : x ^ 14 = x ^ 2 := by
    convert_to (x ^ 3) ^ 4 * x ^ 2 = x ^ 2
    · rw[← pow_mul, ← pow_add]
    · rw[isroot]; ring
  -- and $1/x^14 = 1/x^2 = x/x^3 = x$.
  have xneg2 : 1 / x ^ 2 = x := by
    symm
    rw[eq_div_iff]
    · ring_nf; assumption
    · intro h
      rw[pow_succ] at isroot
      simp[h] at isroot
  -- Thus $x^14 + 1/x^14 = x^2 + x = -1$.
  rw[x14, xneg2]
  rwa[eq_neg_iff_add_eq_zero]