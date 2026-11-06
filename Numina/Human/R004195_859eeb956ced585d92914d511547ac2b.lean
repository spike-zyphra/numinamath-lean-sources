import Mathlib

/-
VIII.2. The sum of all natural numbers from 1 to p is equal to a three-digit number with identical digits. How many natural numbers were there in the summation?
-/

theorem number_theory_241647 (n a:ℕ) (ha:a≤9) (apos: 0 < a)
(h: ∑ i ∈ Finset.Icc 1 n, i = (100*a+10*a+a)): n = 36 := by

  --The sum of first n integers.
  have cla : ∀n:ℕ, ∑ i ∈ Finset.Icc 1 n, i = n*(n+1)/2 := by
    intro n
    induction' n with n hn

    simp

    rw [Finset.sum_Icc_succ_top (by linarith), hn]
    by_cases evenn : Even n
    obtain ⟨k,hk⟩ := evenn
    rw [hk]
    ring_nf
    omega
    have oddn : Odd n := by exact Nat.not_even_iff_odd.mp evenn
    obtain ⟨k,hk⟩ := oddn
    rw [hk]
    ring_nf
    omega
  specialize cla n
  rw [cla] at h

  --By our assumption, we have n(n+1) = 6*37*n.
  have eq : n * (n+1) = a * 6 * 37 := by 
    have t1 : n*(n+1)/2 = 111*a := by linarith
    have t2 : n*(n+1) = 222*a := by 
      have : 222*a = 2*111*a := by ring
      rw [this]
      rw [Nat.mul_assoc, ←t1]
      symm
      rw [mul_comm]
      refine Nat.div_two_mul_two_of_even ?_
      exact Nat.even_mul_succ_self n
    linarith
  
  have dd : 37 ∣ n*(n+1) := by use 6*a; rw [eq]; ring
  have p37: Nat.Prime 37 := by norm_num
  have d37vdd : 37 ∣ n ∨ 37 ∣ n+1 := by exact (Nat.Prime.dvd_mul p37).mp dd
  
  --37 ∣ n or n+1. We divide into two cases and check separately.
  rcases d37vdd with dvd37 | dvd37
  
  obtain ⟨k,hk⟩ := dvd37
  have knne0: k ≠ 0 := by 
    by_contra ke0
    rw [ke0] at hk
    simp at hk
    rw [hk] at eq
    simp at eq
    linarith
  have kl2 : k < 2 := by 
    by_contra nkl2
    have kge2 : 2 ≤ k := by omega
    have : 2*37 ≤ n := by linarith
    nlinarith
  have : k = 1 := by omega
  rw [this] at hk
  simp at hk
  rw [hk] at eq
  omega

  obtain ⟨k,hk⟩ := dvd37
  have knne0: k ≠ 0 := by 
    by_contra ke0
    rw [ke0] at hk
    simp at hk
  have kl2 : k < 2 := by 
    by_contra nkl2
    have kge2 : 2 ≤ k := by omega
    have : 2*37 ≤ n+1 := by linarith
    nlinarith
  have : k = 1 := by omega
  rw [this] at hk
  simp at hk
  rw [hk] at eq
  omega