import Mathlib

/- If $\omega^{1997} = 1$ and $\omega \neq 1,$ then evaluate
\[\frac{1}{1 + \omega} + \frac{1}{1 + \omega^2} + \dots + \frac{1}{1 + \omega^{1997}}.\] -/
/- Note that
\begin{align*}
\frac{1}{1 + \omega^k} + \frac{1}{1 + \omega^{1997 - k}} &= \frac{1}{1 + \omega^k} + \frac{\omega^k}{\omega^k + \omega^{1997}} \\
&= \frac{1}{1 + \omega^k} + \frac{\omega^k}{\omega^k + 1} \\
&= \frac{1 + \omega^k}{1 + \omega^k} = 1.
\end{align*}Thus, we can pair the terms
\[\frac{1}{1 + \omega}, \ \frac{1}{1 + \omega^2}, \ \dots, \ \frac{1}{1 + \omega^{1995}}, \ \frac{1}{1 + \omega^{1996}}\]into $1996/2 = 998$ pairs, so that the sum of the numbers in each pair is 1.  Also, $\frac{1}{1 + \omega^{1997}} = \frac{1}{2},$ so the sum works out to $998 + \frac{1}{2} = \boxed{\frac{1997}{2}}.$ -/
theorem algebra_20696 (ω : ℂ) (hω : ω^1997 = 1) (hω1 : ω ≠ 1) :
    ∑ i ∈ Finset.range 1997, 1 / (1 + ω^(i + 1)) = 1997 / 2 := by
  -- $\frac{1}{1 + \omega} + \frac{1}{1 + \omega^2} + \dots + \frac{1}{1 + \omega^{1997}} = \frac{1}{1 + \omega^{1997}} + \frac{1}{1 + \omega^{1996}} + \dots + \frac{1}{1 + \omega}$
  rw [Finset.sum_range_succ, hω]
  apply add_eq_of_eq_sub
  rw [one_add_one_eq_two, ← sub_div]
  have eq : ∑ i ∈ Finset.range 1996, 1 / (1 + ω^(i + 1)) = ∑ i ∈ Finset.range 1996, 1 / (1 + ω^(1995 - i + 1)) := by
    rw [← Finset.sum_flip]
  field_simp
  rw [mul_two]
  nth_rw 2 [eq]
  rw [← Finset.sum_add_distrib]
  -- $\frac{1}{1 + \omega^x} + \frac{1}{1 + \omega^{1997 - x}} = 1$ for all x
  have eq2 : ∀ x ∈ Finset.range 1996, 1 / (1 + ω ^ (x + 1)) + 1 / (1 + ω ^ (1995 - x + 1)) = 1 := by
    intro x xin
    simp only [Finset.mem_range] at xin
    have omegane : ω ≠ 0 := by
      by_contra contra
      rw [contra] at hω
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_ne_one] at hω
      -- $\frac{1}{1 + \omega^{1997 - k} = \frac{\omega^k}{\omega^k + \omega^{1997}$
    have eq2 : 1 / (1 + ω ^ (1995 - x + 1)) = ω ^ (x + 1) / (ω ^ (x + 1) + ω ^ 1997) := by
      calc
        _ = 1 / (1 + ω ^ (1995 - x + 1)) * (ω ^ (x + 1) / ω ^ (x + 1)) := by
          rw [div_self, mul_one]
          apply pow_ne_zero
          exact omegane
        _ = 1 / (1 + ω ^ (1995 - x + 1)) * ω ^ (x + 1) / ω ^ (x + 1) := by
          ring_nf
        _ = ω ^ (x + 1) / (1 + ω ^ (1995 - x + 1)) / ω ^ (x + 1) := by
          ring_nf
        _ = ω ^ (x + 1) / ((1 + ω ^ (1995 - x + 1)) * ω ^ (x + 1)) := by
          rw [div_div]   
        _ = _ := by
          rw [add_mul, one_mul, ← pow_add, add_assoc (1995 - x), add_comm 1, ← add_assoc (1995 - x), ← add_assoc, Nat.sub_add_cancel (by linarith)]
    rw [eq2, hω, add_comm (ω ^ (x + 1)), ← add_div, div_self]
    -- $1 + \omega ^ (x + 1) \neq 0$
    by_contra contra
    -- Order of $\omega$ divides $1997$
    have dvd : orderOf ω ∣ 1997 := by
      apply orderOf_dvd_of_pow_eq_one hω
    -- for otherwise, Order of $\omega$ divides $2x$
    have dvd2 : orderOf ω ∣ 2 * (x + 1) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [add_comm] at contra
      apply eq_sub_of_add_eq at contra
      rw [zero_sub] at contra
      rw [mul_comm, pow_mul, contra, neg_one_sq]
    -- Order of $\omega$ divides $\gcd(1997, 2x) = 1$, so Order of $\omega$ is $1$
    have ordereq : ω = 1 := by
      have dvd3 : orderOf ω ∣ Nat.gcd 1997 (2 * (x + 1)) := by
        apply Nat.dvd_gcd dvd dvd2
      have gcdeq : Nat.gcd 1997 (2 * (x + 1)) = 1 := by
        apply Nat.Coprime.gcd_eq_one
        apply Nat.coprime_mul_iff_right.mpr
        constructor
        norm_num
        apply Nat.coprime_of_lt_prime
        linarith
        linarith
        norm_num
      rw [gcdeq] at dvd3
      simp only [Nat.dvd_one, orderOf_eq_one_iff] at dvd3
      exact dvd3
    contradiction
  rw [Finset.sum_congr rfl eq2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  norm_num