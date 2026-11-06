import Mathlib

/- For all positive integers $n$, the $n$th triangular number $T_n$ is defined as $T_n = 1+2+3+ \cdots + n$. What is the greatest possible value of the greatest common divisor of $4T_n$ and $n-1$? -/
theorem number_theory_15542 (T : ℕ → ℕ) (hT : ∀ n, T n =
  ∑ i in Finset.Icc 1 n, i) :
  IsGreatest {x | ∃ n, x = Nat.gcd (4 * T n) (n - 1)} 4 := by
  -- since we work on natural numbers, we should prove 2 divide n(n+1) before commute divide and mul.
  have dvd2(d:ℕ): 2 ∣ d*(d+1) := by
    have o1: Odd 1 := by norm_num
    by_cases hhd: Odd d
    · have hh1: Even (d+1) := by
        exact Odd.add_odd hhd o1
      have hh2: 2 ∣ d+1 := by
        exact even_iff_two_dvd.mp hh1
      exact Dvd.dvd.mul_left hh2 d
    · have hh1: Even d := by
        exact Nat.not_odd_iff_even.mp hhd
      have hh2: 2 ∣ d := by
        exact even_iff_two_dvd.mp hh1
      apply Dvd.dvd.mul_right hh2
  -- T n is 1+2+...+n = n(n+1)/2, arithmetic sequence sum.
  have h1: ∀n:ℕ, T n = (n*(n+1))/2 := by
    intro n
    induction' n with d hd
    · simp; have := hT 0 ; simp [this]
    · have ht1: T (d+1) = T d + (d+1) := by
        rw [hT (d+1), hT d]
        apply Finset.sum_Icc_succ_top (by omega)
      rw [ht1, hd]
      have ht3: (d+1) * (d+1+1) = d*(d+1) + 2*(d+1) := by ring
      rw [ht3, Nat.add_div]
      have ht4: d * (d+1) % 2 = 0 := by
        exact (@Nat.dvd_iff_mod_eq_zero 2 (d * (d + 1))).mp (dvd2 d)
      simp [ht4]; norm_num
  -- since T n = n(n+1)/2, 4 T n = 2n(n+1) = 2n^2+2n
  have h2: ∀n:ℕ, 4 * T n = 2*n^2+2*n := by
    intro n; rw [h1 n]
    have ht1: (n*(n+1)) = n*(n+1)/2 * 2 := by
      symm; apply Nat.div_mul_cancel (dvd2 n)
    have ht2: 4*(n*(n+1)/2) = 2*(n*(n+1)) := by
      nth_rw 2 [ht1]; ring
    rw [ht2]; ring
  -- thereby, we can use Euclidean algorithm computing gcd of 2n^2+2n and n-1
  have h3(n:ℕ)(hn:n ≥ 1): Nat.gcd (2*n^2+2*n) (n-1) = Nat.gcd 4 (n-1) := by
    have ht1:2*n^2+2*n = 2*n^2+2*n - (n-1)*(2*n) + (n-1)*(2*n) := by
      have: (n-1)*(2*n) ≤ 2*n^2 + 2*n := by
        have hh1: (n-1)*(2*n) = 2*n^2 - 2*n := by
          rw [Nat.sub_mul]; simp;
          rw [← mul_assoc, mul_comm n 2, mul_assoc, pow_two]
        rw [hh1]; omega
      symm; apply Nat.sub_add_cancel this
    -- 2n^2+2n - 2n(n-1)
    have ht2: Nat.gcd (2*n^2+2*n - (n-1)*(2*n) + (n-1)*(2*n)) (n-1)
      = Nat.gcd (4*n) (n-1) := by
      have: 2*n^2+2*n - (n-1)*(2*n) = 4*n := by
        rw [add_comm, Nat.sub_mul, one_mul]
        have ht1: n*(2*n) ≤ 2*n + 2*n^2 := by linarith
        have ht2: 2*n ≤ n*(2*n) := by
          exact Nat.le_mul_of_pos_left (2 * n) hn
        rw [tsub_tsub_assoc ht1 ht2]
        have: 2*n^2 = n*(2*n) := by ring
        rw [this, Nat.add_sub_assoc (le_refl (n*(2*n)))]
        simp; ring
      rw [this]
      exact Nat.gcd_add_mul_left_left (4 * n) (n - 1) (2 * n)
    -- 4n - 4(n-1)
    have ht3: Nat.gcd (4*n) (n-1) = Nat.gcd 4 (n-1) := by
      have hh1: 4*n = 4*n - 4*(n-1) + 4*(n-1) := by
        have: 4*(n-1) ≤ 4*n := by omega
        symm; apply Nat.sub_add_cancel this
      have hh2: 4*n - 4*(n-1) = 4 := by
        rw [Nat.mul_sub, tsub_tsub_assoc (le_refl (4*n)) (by omega)]
        simp
      rw [hh1, hh2]
      exact Nat.gcd_add_mul_right_left 4 (n - 1) 4
    rw [ht1, ht2, ht3]
  -- thus, we can solve the problem. obviously, gcd 4 n-1 ≤ 4, so maximum is 4, reach maximum when n-1 is multiple of 4, for example, we can use 5.
  rw [IsGreatest, upperBounds]; simp; constructor
  · -- any n satisfy 4 ∣ n-1 is ok. here we use 5.
    use 5
    rw [h2 5, h3 5 (by norm_num)]; simp
  · intro n
    -- if n=0, then gcd is 0, ≤ 4.
    by_cases hn: n = 0
    · rw [h2 n, hn]; simp
    -- when n ≠ 0, n ≥ 1
    · have nge: n ≥ 1 := by omega
      rw [h2 n, h3 n nge]
      apply Nat.gcd_le_left _ (by norm_num)
