import Mathlib

/- Find the largest positive integer $n$ such that
$1+2+3+\cdots+n^{2}$ is divisible by $1+2+$ $3+\cdots+n$. -/
theorem number_theory_611352: IsGreatest {n : ℕ |
    ∑ i ∈ Finset.range n, (1+i) ∣ ∑ i ∈ Finset.range (n^2), (1+i)
  } 1 := by
  -- 1+2+...+m = m(m+1)/2
  have hsum{m:ℕ}: ∑ i ∈ Finset.range m, (1+i) = m * (m+1) / 2 := by
    have := Finset.sum_range_id (1+m)
    rw [Finset.sum_range_add,
    Finset.sum_range_one, zero_add] at this
    rw [this, mul_comm (1+m) _]
    congr 2
    all_goals omega
  -- 2 ∣ m(m+1)
  have even_mul_succ{m:ℕ}: 2 ∣ m*(m+1) := by
    rw [← even_iff_two_dvd]
    exact Nat.even_mul_succ_self m
  constructor
  · -- when n=1, obviously 1 ∣ 1^2
    simp
  · simp only [upperBounds, Set.mem_setOf_eq]
    intro n hdvd
    -- 1+2+...+n = n(n+1)/2
    have h1: ∑ i ∈ Finset.range n, (1+i) = n*(n+1)/2 := hsum
    -- 1+2+...+n^2 = n^2(n^2+1)/2
    have h2: ∑ i ∈ Finset.range (n^2), (1+i) = n^2 * (n^2+1) / 2 := hsum
    -- if n=0, trivial.
    by_cases hn: n = 0
    · simp [hn]
    -- otherwise, the divide relation equivalent to n(n+1) ∣ n^2(n^2+1)
    -- or, n+1 ∣ n^3+n
    replace hdvd: n+1 ∣ n^3+n := by
      have: n*(n+1) ∣ n^2 * (n^2+1) := by
        rw [h1, h2] at hdvd
        have hh1: n*(n+1) = 2 * (n*(n+1)/2) :=
          (Nat.mul_div_cancel' even_mul_succ).symm
        have hh2: n^2*(n^2+1) = 2 * (n^2*(n^2+1)/2) :=
          (Nat.mul_div_cancel' even_mul_succ).symm
        rw [hh1, hh2]
        exact Nat.mul_dvd_mul_left 2 hdvd
      nth_rw 1 [pow_two, mul_assoc] at this
      nth_rw 2 [Nat.mul_add] at this
      rw [mul_one, ← pow_succ'] at this
      norm_num at this
      exact (mul_dvd_mul_iff_left hn).mp this
    -- but n+1 ∣ n^3+n+2, therefore given n+1 ∣ n^3+n, we have n+1 ∣ 2.
    replace hdvd: n+1 ∣ 2 := by
      have: n+1 ∣ n^3+n+2 := by
        -- notice that n^3+n+2 = (n+1)(n^2-n+2)
        have: n^3+n+2 = (n+1)*(n^2-n+2) := by
          have: n ≤ n^2 := Nat.le_self_pow (by norm_num) n
          zify; rw [Nat.cast_sub this]; push_cast
          ring
        rw [this]
        apply Nat.dvd_mul_right
      exact (Nat.dvd_add_iff_right hdvd).mpr this
    -- which leads to n+1 ≤ 2.
    have := Nat.le_of_dvd (by norm_num) hdvd
    -- thus n ≤ 1.
    exact Nat.le_of_lt_succ this