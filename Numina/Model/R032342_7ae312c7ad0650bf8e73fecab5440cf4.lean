import Mathlib

theorem number_theory_19475 {a : ℕ} (ha : a = 2^306 * 3^340) :
    IsGreatest {n | ∃ k, a = k^n} 34 := by
  constructor
  · -- Show 34 is in the set
    use 2 ^ 9 * 3 ^ 10
    rw [ha]
    norm_num
  · -- Show 34 is greatest in the set
    intro n hn
    rcases hn with ⟨k, hk⟩
    rw [ha] at hk
    by_contra h
    push_neg at h
    have h2 : n > 34 := h
    have h3 : k ^ n = 2 ^ 306 * 3 ^ 340 := by linarith
    have h4 : n ∣ 306 := by
      have h6 : n * (k.factorization 2) = 306 := by
        have h5 : (k ^ n).factorization 2 = 306 := by
          rw [h3]
          native_decide
        have h7 : (k ^ n).factorization 2 = n * (k.factorization 2) := by
          rw [Nat.factorization_pow]
          simp
          all_goals omega 
        linarith
      have : n ∣ 306 := by
        use k.factorization 2
        all_goals linarith
      assumption
    have h5 : n ∣ 340 := by
      have h7 : n * (k.factorization 3) = 340 := by
        have h9 : (k ^ n).factorization 3 = 340 := by
          rw [h3]
          native_decide
        have h10 : (k ^ n).factorization 3 = n * (k.factorization 3) := by 
          rw [Nat.factorization_pow]
          simp
          all_goals omega 
        linarith
      have : n ∣ 340 := by
        use k.factorization 3
        all_goals linarith
      assumption
    have h6 : n ∣ 34 := by 
      exact Nat.dvd_gcd h4 h5
    have h7 : n ≤ 34 := by 
      exact Nat.le_of_dvd (by linarith) h6
    linarith