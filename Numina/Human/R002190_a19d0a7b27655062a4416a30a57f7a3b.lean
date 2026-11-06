import Mathlib

open Finset Real Nat

-- we prove a lemma about the sum of a geometric series
lemma lemma_1 (n k: ℕ) (hn: 1 < n) (hk: 0 < k): n ^ k - 1 = (n - 1) * (∑ i ∈ Icc 0 (k - 1), n ^ i) := by

  -- prove by induction
  induction' k with k ih
  -- base case
  .
    simp at hk
  .
    by_cases l: k = 0
    .
      simp [l]
    .
      replace l: 0 < k := by omega
      simp [l] at ih
      rw [show k + 1 - 1 = k - 1 + 1 by omega]
      simp [Finset.sum_Icc_succ_top]
      have s: n ^ k ≤ n ^ (k + 1) := by
        apply Nat.pow_le_pow_of_le_right
        omega
        simp
      have eq: n ^ (k + 1) - 1 = n ^ (k + 1) - n ^ k + (n ^ k - 1) := by
        set a:= n ^ (k + 1)
        set b:= n ^ k
        have r: 1 ≤ b := by
          simp [b]
          apply Nat.one_le_pow
          omega
        omega
      rw [eq]
      clear eq
      rw [ih]
      clear ih
      rw [show k - 1 + 1 = k by omega]
      have t: n ^ (k + 1) - n ^ k = (n - 1) * n ^ k := by
        rw [show n ^ (k + 1) = n * n ^ k by ring]
        set a:= n ^ k
        clear_value a
        have f: a ≤ n * a := by
          nlinarith
        zify
        have o1: ↑(n * a - (a: ℕ)) = ↑(n * a) - (a: ℤ) := by
          apply Int.natCast_sub
          exact f
        rw [o1]
        have o2: ↑(n - (1: ℕ)) = ↑n - (1: ℤ) := by
          apply Int.natCast_sub
          omega
        rw [o2]
        rw [Int.natCast_mul]
        ring
      rw [t]
      clear t
      ring

-- we prove a key inequality which is used in the main theorem
lemma lemma_2 (n: ℕ) (hn: 3 ≤ n): (n - 1)! + 1 < n ^ (n - 1) := by

  have l1: (n - 1)! + 1 < 2 * (n - 1)! := by
    have o: (n - 1) ≤ (n - 1)! := by
      apply Nat.self_le_factorial
    replace o: 1 < (n - 1)! := by
      have o1: 1 < n - 1 := by omega
      nlinarith
    nlinarith

  -- then we prove l2 by induction
  have l2: ∀ x, 2 ≤ x → 2 * (x - 1)! ≤ x ^ (x - 1) := by
    clear l1
    intro x
    induction' x with x ih
    .
      simp
    .
      by_cases l: x < 2
      .
        interval_cases x
        .
          simp
        .
          simp
      .
        replace l: 2 ≤ x := by omega
        simp [l] at ih
        intro y
        rw [show x + 1 - 1 = x - 1 + 1 by omega]
        rw [Nat.factorial_succ]
        rw [show x - 1 + 1 = x by omega]
        replace ih: 2 * (x * (x - 1)!) ≤ x * x ^ (x - 1) := by
          nlinarith
        have o: x * x ^ (x - 1) = x ^ x := by
          symm
          nth_rewrite 2 [show x = x - 1 + 1 by omega]
          rw [Nat.pow_add]
          simp
          ring
        rw [o] at ih
        clear o
        have l2: x ^ x ≤ (x + 1) ^ x := by
          apply Nat.pow_le_pow_of_le_left
          omega
        nlinarith

    --combine l1 and l2
  specialize l2 n (by omega)
  nlinarith

/-Show that there is no positive integer $k$ for which
the equation (n-1)!+1=n^{k} is true when $n$ is greater than $5$.-/

theorem number_theory_71689 (k : ℕ) (hk : 0 < k) :
    ∀ n, n > 5 → ¬(Nat.factorial (n - 1) + 1 = n ^ k) := by

    intro n hn
    by_contra! h

    -- we first show that n is prime
    have pn: Nat.Prime n := by
      by_contra! pn
      apply Nat.exists_dvd_of_not_prime at pn
      obtain ⟨d, d1, d2, d3⟩ := pn
      have o: d ∣ n ^ k := by
        have o1: n ∣ n ^ k := by
          apply dvd_pow_self
          omega
        apply dvd_trans d1 o1
      rw [← h] at o
      have o2: d ∣ Nat.factorial (n - 1) := by
        apply Nat.dvd_factorial
        by_contra! s
        replace s: d = 0 := by omega
        simp [s] at d1
        simp [d1] at hn
        apply Nat.le_of_dvd at d1
        omega
        omega
      have o3: d ∣ 1 := by
        rw [show 1 = Nat.factorial (n - 1) + 1 - Nat.factorial (n - 1) by omega]
        apply Nat.dvd_sub
        omega
        exact o
        exact o2
      apply Nat.le_of_dvd at o3
      have s: d = 0 := by omega
      simp [s] at d1
      simp [d1] at hn
      norm_num
      omega

    have l:= h
    replace h: Nat.factorial (n - 1) = n ^ k - 1 := by
      rw [← h]
      omega
    have d: n - 1 ∣ n ^ k - 1 := by
      rw [lemma_1 n k (by linarith) hk]
      simp
    replace h: (n - 1)! / (n - 1) = (n ^ k - 1) / (n - 1) := by
      rw [h]
    have o1: (n - 1)! / (n - 1) = Nat.factorial (n - 2) := by
      nth_rewrite 1 [show (n - 1) = n - 2 + 1 by omega]
      rw [Nat.factorial_succ]
      rw [show n - 2 + 1 = n - 1 by omega]
      rw [Nat.mul_div_cancel_left]
      omega
    rw [o1] at h
    clear o1

    -- then we mod (n-1) on both sides to get n - 1 ∣ k
    replace h: (n - 2)! % (n - 1) = (n ^ k - 1) / (n - 1) % (n - 1) := by
      rw [h]
    -- show that left side mod (n - 1) is 0
    have m1: (n - 2)! % (n - 1) = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      -- note that n is odd
      have On: Odd n := by
        apply Nat.Prime.odd_of_ne_two
        exact pn
        omega
      apply Odd.exists_bit1 at On
      obtain ⟨b, b1⟩ := On
      simp [b1]
      have i:= Nat.factorial_mul_factorial_dvd_factorial_add 2 b
      have j: 2 * b ∣ (2 + b)! := by
        have j1: 2 * b ∣ 2! * b ! := by
          rw [show 2! = 2 by decide]
          apply Nat.mul_dvd_mul_left
          apply Nat.dvd_factorial
          omega
          simp
        apply dvd_trans j1 i
      have j2: (2 + b)! ∣ (2 * b - 1)! := by
        apply Nat.factorial_dvd_factorial
        omega
      apply dvd_trans j j2
    rw [m1] at h
    clear m1
    -- show that right side mod (n - 1) is k % (n - 1)
    have m2: (n ^ k - 1) / (n - 1) % (n - 1) = k % (n - 1):= by
      rw [lemma_1 n k (by linarith) hk]
      rw [Nat.mul_div_cancel_left]
      rw [Finset.sum_nat_mod]
      clear *- hk hn
      -- prove by induction
      induction' k with k ih
      -- base case
      .
        simp at hk
      .
        by_cases l: k = 0
        .
          simp [l]
        .
          replace l: 0 < k := by omega
          simp [l] at ih
          rw [show k + 1 - 1 = k - 1 + 1 by omega]
          simp [Finset.sum_Icc_succ_top]
          rw [Nat.add_mod]
          rw [ih]
          clear ih
          rw [Nat.add_mod]
          have e: n ^ (k - 1 + 1) % (n - 1) % (n - 1) = 1 := by
            simp
            rw [show k - 1 + 1 = k by omega]
            rw [Nat.pow_mod]
            nth_rewrite 1 [show n = n - 1 + 1 by omega]
            rw [Nat.add_mod]
            rw [show (n - 1) % (n - 1) = 0 by simp]
            rw [show 1 % (n - 1) = 1 by rw [Nat.one_mod_eq_one]; omega]
            simp
            rw [show 1 % (n - 1) = 1 by rw [Nat.one_mod_eq_one]; omega]
            simp
            rw [Nat.one_mod_eq_one]
            omega
          rw [e]
          clear e
          simp
      omega
    rw [m2] at h
    clear m2
    symm at h
    apply Nat.dvd_of_mod_eq_zero at h

    -- hence we have n - 1 ≤ k
    apply Nat.le_of_dvd at h

    -- then we get a size contradiction from l and h
    clear pn d
    have o: n ^ (n - 1) ≤ n ^ k := by
      apply Nat.pow_le_pow_of_le_right
      omega
      exact h
    rw [← l] at o
    clear l h
    absurd o
    simp

    -- finally, we apply lemma_2 to get the contradiction
    apply lemma_2
    omega
    exact hk