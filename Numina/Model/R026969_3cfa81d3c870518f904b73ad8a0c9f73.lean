import Mathlib

theorem number_theory_160199 (n : ℕ) (hn : n > 0) :
    Nat.Coprime (21 * n + 4) (14 * n + 3) := by
  show Nat.Coprime (21 * n + 4) (14 * n + 3)
  have h1 : Nat.Coprime (21 * n + 4) (14 * n + 3) := by
    show Nat.gcd (21 * n + 4) (14 * n + 3) = 1
    have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
      have h2 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (7 * n + 1) := by
        have h3 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (21 * n + 4) := by 
          exact Nat.gcd_dvd_left (21 * n + 4) (14 * n + 3)
        have h4 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (14 * n + 3) := by 
          exact Nat.gcd_dvd_right (21 * n + 4) (14 * n + 3)
        have h5 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (21 * n + 4 - (14 * n + 3)) := by
          apply Nat.dvd_sub' 
          all_goals try exact h3
          all_goals try exact h4
        have h6 : (21 * n + 4 - (14 * n + 3) : ℕ) = 7 * n + 1 := by
          omega 
        rw [h6] at h5 
        exact h5
      have h3 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (1 : ℕ) := by
        have h4 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (7 * n + 1) := h2
        have h5 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (14 * n + 3) := by 
          exact Nat.gcd_dvd_right (21 * n + 4) (14 * n + 3)
        have h6 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ ((14 * n + 3) - 2 * (7 * n + 1) : ℕ) := by 
          apply Nat.dvd_sub' 
          · apply Nat.dvd_trans h5 
            simp 
          · apply Nat.dvd_trans h4 
            norm_num 
        have h7 : ( (14 * n + 3) - 2 * (7 * n + 1) : ℕ) = 1 := by
          omega 
        rw [h7] at h6 
        exact h6 
      have h7 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by 
        exact Nat.dvd_one.mp h3 
      exact h7 
    exact h1
  exact h1