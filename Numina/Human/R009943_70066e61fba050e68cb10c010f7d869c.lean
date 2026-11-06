import Mathlib

/-Compute the sum of all integers 1≤ a ≤ 10 with the following property: there
exist integers p and q such that p, q, p ^ 2 + a and q ^ 2 + a are all distinct
prime numbers -/
theorem number_theory_609541: ∑ᶠ i ∈ {a: ℕ | (1 ≤ a) ∧ (a ≤ 10) ∧ (∃ p q: ℕ, (p < q) ∧ (q ≠ p ^ 2 + a) ∧ 
(Nat.Prime p) ∧ (Nat.Prime q) ∧ (Nat.Prime (p ^ 2 + a)) ∧ (Nat.Prime (q ^ 2 + a)))}, i = 20 := by

 -- we compute the set of a directly
  have h_eq: {a: ℕ | (1 ≤ a) ∧ (a ≤ 10) ∧ (∃ p q: ℕ, (p < q) ∧ (q ≠ p ^ 2 + a) ∧ 
(Nat.Prime p) ∧ (Nat.Prime q) ∧ (Nat.Prime (p ^ 2 + a)) ∧ (Nat.Prime (q ^ 2 + a)))} = {4, 6, 10} := by
    ext a
    simp only [Set.mem_setOf_eq]
    constructor
    -- the forward direction
    . intro h
      simp
      obtain ⟨ha1,ha2,p, q, hpq, hneq, hp, hq, hp2a, hq2a⟩ := h
      have bp: 2 ≤ p := by
        by_contra! no
        replace no: p = 0 ∨ p = 1 := by omega
        rcases no with no | no
        all_goals simp [no] at hp; absurd hp; norm_num
      have bq: 3 ≤ q := by
        omega
      --we show that a must be even
      have h1: Even a := by 
        by_contra! h1
        simp at h1
        apply Nat.Prime.eq_two_or_odd' at hq
        rcases hq with hq | hq
        . omega
        . apply Nat.Prime.eq_two_or_odd' at hq2a
          rcases hq2a with hq2a | hq2a
          . nlinarith
          . replace hq: Odd (q ^ 2) := by
              apply Odd.pow
              exact hq
            absurd hq2a
            simp
            apply Odd.add_odd 
            exact hq
            exact h1
      -- we show that a % 3 ≠ 2
      have h2: a % 3 ≠ 2 := by
        by_contra! h2
        by_cases l: q = 3
        -- q = 3
        . have np: p = 2 := by omega
          simp [np] at hp2a
          apply Nat.Prime.eq_two_or_odd' at hp2a
          rcases hp2a with hp2a | hp2a
          . omega
          . rw [Nat.odd_add'] at hp2a
            have l: Even 4 := by
              decide
            simp [l] at hp2a
            absurd hp2a
            simp [h1]
        -- q ≠ 3
        . have q3: q ^ 2 % 3 = 1 := by
            set r:= q % 3 with hr
            have nr: r = 0 ∨ r = 1 ∨ r = 2 := by
              omega
            rcases nr with nr | nr | nr
            . simp [nr] at hr
              symm at hr
              apply Nat.dvd_of_mod_eq_zero at hr
              rw [Nat.prime_dvd_prime_iff_eq] at hr
              simp [hr]
              omega
              norm_num
              exact hq
            . simp [Nat.pow_mod]
              rw [nr] at hr
              symm at hr
              rw [hr]
            . simp [Nat.pow_mod]
              rw [nr] at hr
              symm at hr
              rw [hr]
          have contra: (q ^ 2 + a) % 3 = 0 := by
             simp [Nat.add_mod,q3,h2]
          apply Nat.dvd_of_mod_eq_zero at contra
          rw [Nat.prime_dvd_prime_iff_eq] at contra
          nlinarith
          norm_num
          exact hq2a
      -- by h1 and h2, we know that a must be 4, 6, or 10
      interval_cases a
      all_goals try omega
      all_goals absurd h1; simp
      all_goals decide
    
  -- the backward direction
    . intro h
      simp at h
      rcases h with h | h | h
      all_goals simp [h]
      . use 3
        use 5
        simp
        norm_num
      . use 5
        use 11
        simp
        norm_num
      . use 3
        use 7
        simp
        norm_num
 

-- finally compute the sum
  rw [h_eq]
  rw [finsum_mem_eq_finite_toFinset_sum]
  simp
  apply Set.toFinite