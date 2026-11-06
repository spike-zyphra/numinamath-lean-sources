import Mathlib

/- Find the sum of all positive integers whose largest proper divisor is 55 .
(A proper divisor of $n$ is a divisor that is strictly less than $n$.) -/
theorem number_theory_609717:
  ∑ᶠ n ∈ {n:ℕ | IsGreatest n.properDivisors 55}, n = 550 := by
  -- if m is the largest proper divisor of n, then exist prime p such that n = mp
  have ex_prime_mul{n m:ℕ}(mpos: 0 < m)(h: IsGreatest n.properDivisors m):
    ∃ p:ℕ, Nat.Prime p ∧ n = m * p := by
    rw [IsGreatest, upperBounds] at h
    norm_cast at h
    have divpos: 0 < n / m := by
      rw [Nat.mem_properDivisors] at h
      apply Nat.div_pos ?_ mpos
      apply le_of_lt h.left.right
    -- m is divisor of n, so m ∣ n.
    have h1: n = m * (n/m) := by
      rw [Nat.mul_div_cancel']
      apply (Nat.mem_properDivisors.mp h.left).left
    -- n/m ≠ 1. otherwise n = m, contradiction to m is proper divisor.
    have h2: n/m ≠ 1 := by
      by_contra!
      rw [this, mul_one] at h1
      replace := Nat.mem_properDivisors.mp h.left
      simp [h1] at this
    -- and we claim n/m is prime. otherwise m is not the largest proper divisor.
    replace h2: Nat.Prime (n/m) := by
      rcases (Nat.exists_prime_and_dvd h2) with ⟨p, pp, pdvd⟩
      by_cases hp: n/m = p
      · rwa [hp]
      · push_neg at hp
        -- p divide n/m, n/m divide n, so p divide n.
        have pdvdn: p ∣ n := by
          apply Nat.dvd_trans pdvd ?_
          nth_rw 2 [h1]
          apply Nat.dvd_mul_left
        -- p < n/m, so n/p > m
        have h3: n/p > m := by
          refine (Nat.lt_div_iff_mul_lt' pdvdn m).mpr ?_
          rw [h1, mul_comm p m]
          refine Nat.mul_lt_mul_of_pos_left ?_ mpos
          apply lt_of_le_of_ne ?_ hp.symm
          apply Nat.le_of_dvd divpos pdvd
        -- but we suppose m is largest proper divisor, contradiction.
        have not_h3: n/p ≤ m := by
          simp only [Nat.mem_properDivisors, and_imp,
          Set.mem_setOf_eq] at h
          apply h.right ?_ ?_
          · exact Nat.div_dvd_of_dvd pdvdn
          · refine Nat.div_lt_self ?_ pp.one_lt
            -- 0 < m, 0 < n/m, then 0 < n.
            omega
        linarith only [h3, not_h3]
    -- therefore n/m satisfy the conditions.
    exact ⟨n/m, h2, h1⟩
  -- therefore, if 55 is the greatest properdivisor of n, then n can be written as 55p.
  -- but p cannot exceed 5, otherwise 55 is not the greatest proper divisor
  -- prime number ≤ 5 is exactly 2,3,5.
  have ex_prime_mul_55{n:ℕ}(h: IsGreatest n.properDivisors 55):
    n = 2*55 ∨ n = 3*55 ∨ n = 5*55 := by
    have: 0 < 55 := by norm_num
    rcases (ex_prime_mul this h) with ⟨p, pp, hnp⟩
    rw [IsGreatest, upperBounds] at h
    norm_cast at h
    -- p ≤ 5, otherwise 55 is not greatest properdivisor.
    have ple: p ≤ 5 := by
      -- suppose on the contrary, p > 5.
      by_contra! pgt5
      have hn: n/5 ∈ n.properDivisors := by
        rw [Nat.mem_properDivisors, hnp]
        constructor
        · apply Nat.div_dvd_of_dvd ?_
          apply Dvd.dvd.mul_right (by norm_num)
        · refine Nat.div_lt_self ?_ (by norm_num)
          simp [pp.pos]
      -- we suppose 55 = n/p is largest proper divisor, so n/5 ≤ 55.
      have h: n/5 ≤ n/p := by
        have: n/p = 55 := by
          rw [hnp]
          simp [pp.ne_zero]
        rw [this]
        apply h.right hn
      -- but p > 5, therefore n/5 > n/p, contradiction.
      have not_h: n/5 > n/p := by
        have h1: n/5 = 11*p := by
          rw [hnp]
          omega
        have h2: n/p = 11*5 := by
          rw [hnp]
          simp [pp.ne_zero]
        rw [h1, h2]
        apply (Nat.mul_lt_mul_left (by norm_num)).mpr pgt5
      linarith only [h, not_h]
    -- prime number ≤ 5 can only be 2,3,5
    have: p = 2 ∨ p = 3 ∨ p = 5 := by
      clear * - pp ple
      revert pp; revert p
      decide
    rw [hnp]
    rcases this with (rfl | rfl | rfl)
    all_goals simp
  -- then we claim set of numbers has 55 as its greatest divisors are 2x55, 3x55, 5x55.
  have: {n:ℕ | IsGreatest n.properDivisors 55} = {2*55, 3*55, 5*55} := by
    ext n
    constructor
    · intro h
      apply ex_prime_mul_55 h
    · -- verify 2x55, 3x55, 5x55 has 55 as its largest properdivisors.
      simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, IsGreatest, Finset.mem_coe,
      Nat.mem_properDivisors, upperBounds, and_imp, Set.mem_setOf_eq]
      -- prove any proper divisor a of 2x55, 3x55, 5x55 ≤ 55.
      rintro (rfl | rfl | rfl)
      all_goals
        refine ⟨(by norm_num), ?_⟩
        intro a advd alt
        -- suppose ak = 2x55, 3x55, 5x55.
        rcases advd with ⟨k, hk⟩
        -- k cannot be 1, otherwise a is not proper divisor. so k > 1.
        have kgt: k > 1 := by
          rw [hk] at alt
          exact one_lt_of_lt_mul_right alt
        -- to prove a ≤ 55, suffices to prove ak ≤ 55k.
        suffices a*k ≤ k*55 by
          rw [mul_comm k 55] at this
          apply Nat.le_of_mul_le_mul_right this (Nat.zero_lt_of_lt kgt)
        rw [← hk]
        -- k divide ak = 2x55,3x55,5x55, and prime factor of right side is 5,11 (and 2, 3.)
        -- so minimum value of k is 2 or 3 or 5.
        have kdvd: k ∣ a*k := Nat.dvd_mul_left _ _
        rw [← hk] at kdvd
        apply Nat.mul_le_mul_right
      · exact kgt
      · by_cases keq: k = 2
        · norm_num [keq] at kdvd
        -- k > 1, k ≠ 2, so k ≥ 3.
        omega
      · by_contra! kle
        -- k divide 5x55 = 5^2 x 11, impossible if k < 5.
        replace kle: k ≤ 4 := Nat.le_of_lt_succ kle
        interval_cases k
        all_goals norm_num at kdvd
  -- therefore sum of these numbers is 2x55 + 3x55 + 5x55 = 550
  rw [this, finsum_mem_insert, finsum_mem_insert]
  all_goals simp