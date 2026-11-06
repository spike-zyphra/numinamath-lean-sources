import Mathlib

theorem number_theory_73195 (a d : ℤ) (ha : Prime a) (hd : Prime (a + d))
    (h2d : Prime (a + 2 * d)) (h3a : 3 < a) (h3d : 3 < a + d) (h32d : 3 < a + 2 * d) :
    6 ∣ d := by

  have h4 : a % 2 = 1 := by
    by_contra h
    push_neg at h 
    have h6 : a % 2 = 0 := by 
      omega 
    have h7 : ¬ (Prime a) := by
      have h11 : a % 2 = 0 := h6
      have h12 : a > 2 := by
        omega 
      have h13 : ¬ (Prime a) := by 
        rw [Int.prime_iff_natAbs_prime] at ha ⊢
        have h14 : (a.natAbs) % 2 = 0 := by 
          omega
        have h15 : ¬ (Nat.Prime (a.natAbs)) := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (a.natAbs) by 
            omega 
          )
          all_goals
            omega 
        tauto 
      exact h13 
    tauto

  have h5 : (a + d) % 2 = 1 := by 
    by_contra h 
    push_neg at h 
    have h8 : (a + d) % 2 = 0 := by 
      omega 
    have h10 : ¬ (Prime (a + d)) := by 
      have h11 : (a + d) % 2 = 0 := h8 
      have h12 : (a + d) > 2 := by
        omega 
      have h13 : ¬ (Prime (a + d)) := by
        rw [Int.prime_iff_natAbs_prime] at hd ⊢ 
        have h14 : ( (a + d).natAbs ) % 2 = 0 := by
          omega 
        have h15 : ¬ (Nat.Prime ( (a + d).natAbs )) := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ ( (a + d).natAbs ) by
            omega 
          )
          all_goals
            omega 
        tauto 
      exact h13 
    tauto

  have h6 : d % 2 = 0 := by 
    omega

  have h7 : a % 3 = 1 ∨ a % 3 = 2 := by
    by_contra h 
    push_neg at h 
    have h8 : a % 3 = 0 := by 
      omega 
    have h9 : ¬ (Prime a) := by 
      have h10 : a % 3 = 0 := h8
      have h11 : a > 3 := by 
        omega
      have h12 : ¬ (Prime a) := by 
        rw [Int.prime_iff_natAbs_prime] at ha ⊢ 
        have h13 : (a.natAbs) % 3 = 0 := by 
          omega
        have h14 : ¬ (Nat.Prime (a.natAbs)) := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (a.natAbs) by 
            omega 
          )
          all_goals 
            omega 
        tauto 
      exact h12
    tauto

  have h8 : (a + d) % 3 = 1 ∨ (a + d) % 3 = 2 := by 
    by_contra h
    push_neg at h 
    have h9 : (a + d) % 3 = 0 := by 
      omega 
    have h10 : ¬ (Prime (a + d)) := by
      have h11 : (a + d) % 3 = 0 := h9
      have h12 : (a + d) > 3 := by 
        omega 
      have h13 : ¬ (Prime (a + d)) := by
        rw [Int.prime_iff_natAbs_prime] at hd ⊢
        have h14 : ( (a + d).natAbs ) % 3 = 0 := by 
          omega
        have h15 : ¬ (Nat.Prime ( (a + d).natAbs )) := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ ( (a + d).natAbs ) by 
            omega 
          )
          all_goals
            omega 
        tauto 
      exact h13
    tauto

  have h9 : (a + 2 * d) % 3 = 1 ∨ (a + 2 * d) % 3 = 2 := by
    by_contra h
    push_neg at h 
    have h10 : (a + 2 * d) % 3 = 0 := by 
      omega 
    have h11 : ¬ (Prime (a + 2 * d)) := by
      have h12 : (a + 2 * d) % 3 = 0 := h10 
      have h13 : (a + 2 * d) > 3 := by 
        omega 
      have h14 : ¬ (Prime (a + 2 * d)) := by
        rw [Int.prime_iff_natAbs_prime] at h2d ⊢
        have h15 : ( (a + 2 * d).natAbs ) % 3 = 0 := by 
          omega 
        have h16 : ¬ (Nat.Prime ( (a + 2 * d).natAbs )) := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ ( (a + 2 * d).natAbs ) by 
            omega 
          )
          all_goals 
            omega 
        tauto 
      exact h14 
    tauto

  have h10 : d % 3 = 0 := by 
    omega

  omega