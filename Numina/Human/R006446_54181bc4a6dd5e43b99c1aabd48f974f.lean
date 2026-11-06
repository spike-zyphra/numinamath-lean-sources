import Mathlib

open scoped Nat

/- consider number of ways partition kN items into k groups of N items each. or refer to multinomial coefficient.  -/
lemma l_factorial_pow_mul_factorial_dvd_mul_factorial {k N: ℕ} (hN: N ≠ 0):
  (N !)^k * (k !) ∣ (k * N) ! := by
  induction' k with k ih
  · simp
  · have h1: (N !)^(k+1) * (k+1) ! =
      ((N !)^k * k !) * (N ! * (k+1)) := by
      rw [pow_succ, Nat.factorial_succ]
      ring
    have h2: ((k+1)*N) ! = (k*N) ! * (k*N+1).ascFactorial N := by
      nth_rw 1 [show k*N = k*N+1-1 by simp]
      rw [Nat.factorial_mul_ascFactorial' _ _ (by simp)]
      congr 1
      simp only [Nat.add_one_mul, Nat.succ_add_sub_one, Nat.add_left_cancel_iff]
    have h3: (N ! * (k+1)) ∣ (k*N+1).ascFactorial N := by
      rw [Nat.ascFactorial_eq_factorial_mul_choose,
      ← Nat.add_one_mul]
      suffices (k+1) ∣ ((k+1)*N).choose N by
        apply Nat.mul_dvd_mul dvd_rfl this
      rw [Nat.choose_mul_right hN]
      apply Nat.dvd_mul_right
    rw [h1, h2]
    apply Nat.mul_dvd_mul ih h3

/- Let $k$ and $m$ be non-negative integers. Show that $(k^m)!$ (the factorial of $k^m$) is divisible by $(k!)^{\sum_{i=0}^{m-1} k^i}$ (the factorial of $k$, raised to the power of the sum $\sum_{i=0}^{m-1} k^i$).
(Conventions: $0^0=1$. For $m=0$, the sum $\sum_{i=0}^{m-1} k^i$ is an empty sum, equal to 0. Thus, for $m=0$, the exponent is 0, and $(k!)^0 = 1$.) -/
theorem number_theory_637154 {k m : ℕ} :
  ((k !) ^ (∑ i ∈ Finset.range m, k ^ i)) ∣ (k ^ m)! := by

  -- k = 0, trivial.
  by_cases hk: k = 0
  · simp [hk]

  -- else, induction on m.
  induction' m with m ih
  · simp
  · -- k^0+k^1+...+k^m = 1 + k (k^0+k^1+...+k^(m-1))
    have h1: ∑ i ∈ Finset.range (m+1), k^i =
      1 + k * (∑ i ∈ Finset.range m, k^i) := by
      rw [Finset.sum_range_succ', add_comm 1 _]
      simp only [pow_zero, Finset.mul_sum,
      ← pow_succ', Nat.add_left_cancel_iff]
    -- from lemma we proved before, (k^m !)^k k! divide (k k^m)!
    have h2: ((k^m) !)^k * k ! ∣ (k * k^m) ! := by
      apply l_factorial_pow_mul_factorial_dvd_mul_factorial ?_
      simp [hk]
    rw [h1, pow_add, pow_one, pow_succ']
    nth_rw 1 [mul_comm k _, pow_mul, mul_comm (k !) _]
    -- use inductive hypothesis, done.
    refine Dvd.dvd.trans ?_ h2
    apply Nat.mul_dvd_mul ?_ dvd_rfl
    exact (Nat.pow_dvd_pow_iff hk).mpr ih