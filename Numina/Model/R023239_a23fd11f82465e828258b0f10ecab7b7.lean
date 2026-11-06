import Mathlib

theorem number_theory_189677 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : m^2 = ∑ i in Finset.Icc 1 n, Nat.factorial i) :
    (m, n) = (1, 1) ∨ (m, n) = (3, 3) := by 
  by_cases hn1 : n ≤ 3
  · -- Case n ≤ 3
    have hn2 : n = 1 ∨ n = 2 ∨ n = 3 := by
      omega 
    rcases hn2 with (hn2 | hn2 | hn2)

    · -- n = 1 
      rw [hn2] at h 
      norm_num [Finset.sum_Icc_succ_top, Nat.factorial] at h 
      have hm1 : m = 1 := by 
        nlinarith 
      left 
      simp [hm1, hn2]

    · -- n = 2 
      rw [hn2] at h 
      norm_num [Finset.sum_Icc_succ_top, Nat.factorial] at h 
      exfalso 
      have h9 : m ≤ 1 := by nlinarith 
      have hm1 : m = 1 := by 
        interval_cases m <;> try { 
          omega 
        }
      rw [hm1] at h 
      all_goals omega 

    · -- n = 3 
      rw [hn2] at h 
      norm_num [Finset.sum_Icc_succ_top, Nat.factorial] at h 
      have hm1 : m = 3 := by 
        nlinarith 
      right 
      simp [hm1, hn2]
  · -- Case n > 3
    have h6 : n ≥ 4 := by 
      omega 
    have h5 : (∑ i in Finset.Icc 1 n, Nat.factorial i) % 5 = 3 := by 
      have h8 : ∀ k : ℕ, (∑ i in Finset.Icc 1 (k + 4), Nat.factorial i) % 5 = 3 := by 
        intro k 
        induction k with 
        | zero =>
          norm_num [Finset.sum_Icc_succ_top, Nat.factorial]
        | succ k ih =>
          rw [show k + 1 + 4 = (k + 4) + 1 by omega]
          rw [Finset.sum_Icc_succ_top (by linarith)]
          have h3 : (Nat.factorial ((k + 4) + 1)) % 5 = 0 := by
            have h4 : (k + 4) + 1 ≥ 5 := by 
              omega 
            have h5 : 5 ∣ Nat.factorial ((k + 4) + 1) := by 
              apply Nat.dvd_factorial 
              all_goals linarith 
            omega 
          simp [Nat.add_mod, h3, ih] at *
      specialize h8 (n - 4)
      have hn2 : n - 4 + 4 = n := by 
        omega 
      rw [hn2] at h8 
      omega 
    have h7 : m ^ 2 % 5 = 0 ∨ m ^ 2 % 5 = 1 ∨ m ^ 2 % 5 = 4 := by
      have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
        omega 
      rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> simp [Nat.pow_mod, Nat.mul_mod, h1, Nat.add_mod]
    have h8 : m ^ 2 % 5 = 3 := by 
      omega 
    omega