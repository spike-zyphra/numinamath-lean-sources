import Mathlib

/- 7. (2004 National High School Mathematics Competition) Given the sequence $a_{0}, a_{1}, a_{2}, \cdots, a_{n}, \cdots$ satisfies the relation (3$\left.a_{n+1}\right)\left(6+a_{n}\right)=18$, and $a_{0}=3$, then the value of $\sum_{i=0}^{n} \frac{1}{a_{i}}$ is $\qquad$ . -/
theorem algebra_231992 {a : ℕ → ℝ} (ha : ∀ n, (3 - a (n + 1)) * (6 + a n) = 18) (ha0 : a 0 = 3) :
    ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 3 := by
    -- let's first show all of the terms are positive
    have h0: ∀ n, a n > 0 := fun n => by
      induction n with
      | zero => linarith [ha0]
      | succ n hn =>
        specialize ha n
        nlinarith
    -- we then show 1/(a_{n+1})+1/3 = 2*(1/(a_{n}+1/3), aka we can find a geometric series
    have h1:∀ n, 1/(a (n+1))+1/3 = 2*(1/a n+1/3) := by
      intro n
      field_simp [(show a n ≠ 0 by exact Ne.symm (ne_of_lt (h0 n))), (show a (n+1) ≠ 0 by exact Ne.symm (ne_of_lt (h0 (n+1))))]
      linarith [ha n]

    -- since we observe a geometric series we can easily compute the nth term of it
    have h2:∀ n, 1/a n + 1/3 = 2/3*2^n := fun n => by
      induction n with
      | zero => simp [ha0]; norm_num
      | succ n hn =>
        rw [h1 n, hn]
        ring_nf
    have h3: ∀ n, 1/a n = (2 * 2^n-1)/3 := fun n => by
      linarith [h2 n]
    simp_rw [h3]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, geom_sum_eq, ← Finset.nsmul_eq_sum_const]
    ring_nf; norm_num