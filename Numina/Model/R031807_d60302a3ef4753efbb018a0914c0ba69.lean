import Mathlib

theorem number_theory_16169 :
    IsLeast {x | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.gcd m n = 12 ∧ x = Nat.gcd (10 * m) (15 * n)} 60 := by
  constructor
  · -- Show 60 is in the set
    use 12, 12
    all_goals norm_num
  · -- Show 60 is the least
    intro x hx
    rcases hx with ⟨m, n, hm, hn, h1, hx⟩
    have h2 : 12 ∣ m := by 
      have h3 : Nat.gcd m n ∣ m := by 
        apply Nat.gcd_dvd_left 
      rw [show Nat.gcd m n = 12 by exact h1] at h3 
      exact h3 
    have h3 : 12 ∣ n := by 
      have h5 : Nat.gcd m n ∣ n := by 
        apply Nat.gcd_dvd_right 
      rw [show Nat.gcd m n = 12 by exact h1] at h5 
      exact h5 
    rcases h2 with ⟨k, hk⟩ 
    rcases h3 with ⟨l, hl⟩ 
    have h4 : Nat.gcd m n = 12 := h1
    rw [show m = 12 * k by omega, show n = 12 * l by omega] at h4
    have h5 : Nat.gcd (12 * k) (12 * l) = 12 * (Nat.gcd k l) := by 
      rw [Nat.gcd_mul_left]
      all_goals norm_num
    rw [h5] at h4 
    have h6 : Nat.gcd k l = 1 := by 
      linarith 
    have h8 : Nat.gcd (10 * m) (15 * n) = 60 * (Nat.gcd (2*k) (3*l)) := by
      rw [show m = 12 * k by omega, show n = 12 * l by omega]
      have h8 : Nat.gcd (10 * (12 * k)) (15 * (12 * l)) = 60 * (Nat.gcd (2*k) (3*l)) := by
        have h9 : 10 * (12 * k) = 60 * (2 * k) := by
          omega
        have h10 : 15 * (12 * l) = 60 * (3 * l) := by 
          omega 
        rw [h9, h10]
        rw [Nat.gcd_mul_left]
        all_goals norm_num 
      exact h8 
    have h9 : Nat.gcd (2*k) (3*l) ≥ 1 := by 
      have h7 : Nat.gcd k l = 1 := h6 
      have h10 : Nat.gcd (2*k) (3*l) ≥ 1 := by 
        apply Nat.gcd_pos_of_pos_left 
        omega 
      linarith 
    linarith [h8, hx, h9]