import Mathlib

open Complex

/- $12 \cdot 37$ Let $i=\sqrt{-1}$, the complex sequence $z_{1}=0, n \geqslant 1$ when, $\approx_{n+1}=$ $z_{n}^{2}+i$. Then the modulus of $z_{111}$ in the complex plane is
(A) 1 .
(B) $\sqrt{2}$.
(C) $\sqrt{3}$.
(D) $\sqrt{110}$.
(E) $\sqrt{2^{55}}$.
(43rd American High School Mathematics Examination, 1992) -/
theorem algebra_197494 (z : ℕ → ℂ)
  (hz0 : z 0 = 0) (hzn : ∀ n, z (n + 1) = z n ^ 2 + I) :
  abs (z 110) = Real.sqrt 2 := by
  -- we'll prove for all even n ≥ 2, z(n) = -1 + I, a way to say that is to say z(2*n+2) is always -1 + I, we'll prove using inducction
  have aux (n : ℕ) : z (2 * n + 2) = -1 + I := by
    induction' n with m hm
    . norm_num
      rw [hzn, hzn, hz0]
      simp
    . rw [hzn, hzn, show 2*(m+1) = 2*m + 2 by ring, hm]
      ring_nf
      simp [show I^3 = I^2 * I by ring]
      ring
  -- now write 110 as 2*54+2 and apply the result
  rw [show 110 = 2 * 54 + 2 by norm_num]
  rw [aux, abs_def]
  simp only
  rw [normSq_apply]
  simp only [add_re, neg_re, one_re, I_re, add_zero, mul_neg, mul_one, neg_neg, add_im, neg_im,
    one_im, neg_zero, I_im, zero_add, nonneg_add_self_iff, zero_le_one, Nat.ofNat_nonneg,
    Real.sqrt_inj]
  norm_num