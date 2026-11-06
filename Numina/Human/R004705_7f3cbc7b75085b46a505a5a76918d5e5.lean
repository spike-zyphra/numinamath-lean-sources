import Mathlib

/-The largest even number that cannot be expressed as the sum of two odd composite numbers is 38-/
theorem number_theory_306545 :
  IsGreatest {n : ℕ | Even n ∧ ¬∃ c1 c2 : ℕ,
  Odd c1 ∧ Odd c2 ∧ c1 + c2 = n ∧ ¬Nat.Prime c1 ∧ ¬Nat.Prime c2} 38 := by
  constructor
  -- First part: show 38 is in the set
  · simp
    constructor
    · exact Nat.even_iff.mpr rfl
    -- Show 38 cannot be written as sum of two odd non-primes
    · intro x1 hx1 x2 hx2 hs hp
      have : x1 ≤ 38 := by omega
      rw [show x2 = 38 - x1 by omega]
      rw [show x2 = 38 - x1 by omega] at hx2
      -- Check all possible values of x1 by cases
      interval_cases x1
      all_goals
        rw [Nat.odd_iff] at hx2
        norm_num at hx2 hp ⊢
  -- Second part: show 38 is the greatest such number
  · intro n hn
    simp at hn
    obtain ⟨h1, h0⟩ := hn
    by_contra w
    -- Show n%10 cannot be 0 (contradiction via divisibility by 5)
    have hd0 : n % 10 ≠ 0 := by
      by_contra h
      have h2 : Nat.Prime (n - 15) := by
        apply h0 15
        exact Nat.odd_iff.mpr rfl
        refine Nat.Even.sub_odd (by linarith) h1 ?_
        rw [Nat.odd_iff]
        refine Nat.add_sub_of_le (by linarith)
        norm_num
      -- Show n-15 is divisible by 5, contradicting primality
      have h3 : 5 ∣ (n - 15) := by omega
      have h4 : n - 15 > 5 := by omega
      have h5 : ¬Nat.Prime (n - 15) := by
        refine (Nat.not_prime_iff_exists_dvd_ne ?_).mpr ?_
        linarith
        use 5
        omega
      exact h5 h2
    -- Show n%10 cannot be 2 (similar argument)
    have hd2 : n % 10 ≠ 2 := by
      by_contra h
      have h2 : Nat.Prime (n - 27) := by
        apply h0 27
        exact Nat.odd_iff.mpr rfl
        refine Nat.Even.sub_odd (by linarith) h1 ?_
        rw [Nat.odd_iff]
        refine Nat.add_sub_of_le (by linarith)
        norm_num
      -- Show n-27 is divisible by 5
      have h3 : 5 ∣ (n - 27) := by omega
      have h4 : n - 27 > 5 := by omega
      have h5 : ¬Nat.Prime (n - 27) := by
        refine (Nat.not_prime_iff_exists_dvd_ne ?_).mpr ?_
        linarith
        use 5
        omega
      exact h5 h2
    -- Show n%10 cannot be 4
    have hd4 : n % 10 ≠ 4 := by
      by_contra h
      have h2 : Nat.Prime (n - 9) := by
        apply h0 9
        exact Nat.odd_iff.mpr rfl
        refine Nat.Even.sub_odd (by linarith) h1 ?_
        rw [Nat.odd_iff]
        refine Nat.add_sub_of_le (by linarith)
        norm_num
      -- Show n-9 is divisible by 5
      have h3 : 5 ∣ (n - 9) := by omega
      have h4 : n - 9 > 5 := by omega
      have h5 : ¬Nat.Prime (n - 9) := by
        refine (Nat.not_prime_iff_exists_dvd_ne ?_).mpr ?_
        linarith
        use 5
        omega
      exact h5 h2
    -- Show n%10 cannot be 6
    have hd6 : n % 10 ≠ 6 := by
      by_contra h
      have h2 : Nat.Prime (n - 21) := by
        apply h0 21
        exact Nat.odd_iff.mpr rfl
        refine Nat.Even.sub_odd (by linarith) h1 ?_
        rw [Nat.odd_iff]
        refine Nat.add_sub_of_le (by linarith)
        norm_num
      -- Show n-21 is divisible by 5
      have h3 : 5 ∣ (n - 21) := by omega
      have h4 : n - 21 > 5 := by omega
      have h5 : ¬Nat.Prime (n - 21) := by
        refine (Nat.not_prime_iff_exists_dvd_ne ?_).mpr ?_
        linarith
        use 5
        omega
      exact h5 h2
    -- Show n%10 cannot be 8
    have hd8 : n % 10 ≠ 8 := by
      by_contra h
      have h2 : Nat.Prime (n - 33) := by
        apply h0 33
        exact Nat.odd_iff.mpr rfl
        refine Nat.Even.sub_odd (by linarith) h1 ?_
        rw [Nat.odd_iff]
        refine Nat.add_sub_of_le (by linarith)
        norm_num
      -- Show n-33 is divisible by 5
      have h3 : 5 ∣ (n - 33) := by omega
      have h4 : n - 33 > 5 := by omega
      have h5 : ¬Nat.Prime (n - 33) := by
        refine (Nat.not_prime_iff_exists_dvd_ne ?_).mpr ?_
        linarith
        use 5
        omega
      exact h5 h2
    -- Final contradiction: even numbers can only end in 0,2,4,6,8
    have h2 : n % 2 = 0 := Nat.even_iff.mp h1
    have h3 : (n % 10) % 2 = 0 := by omega
    have h4 : n % 10 < 10 := Nat.mod_lt n (by norm_num)
    omega
