import Mathlib

theorem number_theory_154743 (n : ℕ) :
    Nat.gcd (21*n+4) (14*n+1) = 1 ↔ ¬(n ≡ 1 [MOD 5]) := by
  constructor
  · -- Assume gcd (21 * n + 4) (14 * n + 1) = 1, prove ¬(n ≡ 1 [MOD 5])
    intro h
    by_contra h1
    -- Assume n ≡ 1 [MOD 5], derive a contradiction
    have h2 : n % 5 = 1 := by 
      simp [Nat.ModEq] at h1 
      omega 
    have h3 : (21 * n + 4) % 5 = 0 := by 
      omega 
    have h4 : (14 * n + 1) % 5 = 0 := by 
      omega 
    have h5 : 5 ∣ (21 * n + 4) := by 
      omega 
    have h6 : 5 ∣ (14 * n + 1) := by 
      omega 
    have h7 : 5 ∣ Nat.gcd (21 * n + 4) (14 * n + 1) := by 
      apply Nat.dvd_gcd 
      · exact h5 
      · exact h6 
    have h8 : 5 ∣ 1 := by 
      rw [h] at h7 
      exact h7 
    have h9 : 5 ≤ 1 := by 
      omega 
    all_goals linarith 
  · -- Assume ¬(n ≡ 1 [MOD 5]), prove gcd (21 * n + 4) (14 * n + 1) = 1 
    intro h 
    have h1 : n % 5 ≠ 1 := by 
      by_contra h2 
      have h1 : n ≡ 1 [MOD 5] := by 
        simp [Nat.ModEq] 
        omega 
      contradiction 
    have h2 : Nat.gcd (21 * n + 4) (14 * n + 1) ∣ 21 * n + 4 := by 
      apply Nat.gcd_dvd_left 
    have h3 : Nat.gcd (21 * n + 4) (14 * n + 1) ∣ 14 * n + 1 := by 
      apply Nat.gcd_dvd_right 
    -- Show that the GCD divides 5 
    have h4 : Nat.gcd (21 * n + 4) (14 * n + 1) ∣ (2 * (21 * n + 4) - 3 * (14 * n + 1)) := by 
      apply Nat.dvd_sub' 
      · -- Show that $ \gcd(21 * n + 4, 14 * n + 1) \mid 2 * (21 * n + 4) $ 
        apply Dvd.dvd.mul_left 
        exact h2 
      · -- Show that $ \gcd(21 * n + 4, 14 * n + 1) \mid 3 * (14 * n + 1) $ 
        apply Dvd.dvd.mul_left 
        exact h3 
    have h5 : 2 * (21 * n + 4) - 3 * (14 * n + 1) = 5 := by 
      omega 
    have h6 : Nat.gcd (21 * n + 4) (14 * n + 1) ∣ 5 := by 
      rw [h5] at h4 
      exact h4 
    have h7 : Nat.gcd (21 * n + 4) (14 * n + 1) ≤ 5 := by 
      apply Nat.le_of_dvd (by norm_num) h6 
    interval_cases h8 : Nat.gcd (21 * n + 4) (14 * n + 1) <;> norm_num at h6 h8 <;> try { 
      all_goals 
        try { 
          simp_all [h8] 
          <;> omega 
        } 
    }